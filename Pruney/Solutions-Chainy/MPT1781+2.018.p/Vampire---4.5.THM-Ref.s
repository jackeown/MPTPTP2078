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
% DateTime   : Thu Dec  3 13:19:20 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  352 (637521573 expanded)
%              Number of leaves         :   12 (116942540 expanded)
%              Depth                    :  106
%              Number of atoms          : 1370 (4675235986 expanded)
%              Number of equality atoms :  466 (603533777 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1591,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1563,f1311])).

fof(f1311,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1220,f1296])).

fof(f1296,plain,(
    k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f1224,f1220])).

fof(f1224,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(backward_demodulation,[],[f593,f1214])).

fof(f1214,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1125,f536])).

fof(f536,plain,(
    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f97,f527])).

fof(f527,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f451,f97])).

fof(f451,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f35,f440])).

fof(f440,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f434,f439])).

fof(f439,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f438,f278])).

fof(f278,plain,
    ( k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f277,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f269,f105])).

fof(f105,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f102,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f34,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f269,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f192,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f192,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f191,f117])).

fof(f117,plain,(
    v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f92,f58])).

fof(f92,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f191,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f86])).

fof(f86,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f84,f40])).

fof(f84,plain,
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

fof(f181,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f48,f175])).

fof(f175,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f135,f139])).

fof(f139,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f110,f104])).

fof(f104,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f95,f101])).

fof(f101,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f34,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) ),
    inference(subsumption_resolution,[],[f93,f34])).

fof(f93,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f33,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f92])).

fof(f108,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f89,f64])).

fof(f89,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,
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

fof(f135,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f114,f104])).

fof(f114,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f92,f54])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(f438,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f437,f86])).

fof(f437,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f436,f117])).

fof(f436,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f429,f250])).

fof(f250,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f249,f105])).

fof(f249,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f247,f32])).

fof(f247,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f245,f49])).

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

fof(f245,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f32])).

fof(f244,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f238,f105])).

fof(f238,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f188,f67])).

fof(f188,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f117])).

fof(f187,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f86])).

fof(f179,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f47,f175])).

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

fof(f429,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f428,f281])).

fof(f281,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f280,f224])).

fof(f224,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f105])).

fof(f223,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f217,f32])).

fof(f217,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f186,f67])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f86])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f117])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f47,f175])).

fof(f280,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f256,f104])).

fof(f256,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f235,f31])).

fof(f31,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f235,plain,
    ( m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f224,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f99,f104])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f79,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f74,f40])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f428,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f266,f369])).

fof(f369,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f362,f368])).

fof(f368,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f367,f278])).

fof(f367,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f366,f86])).

fof(f366,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f365,f117])).

fof(f365,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f346,f250])).

fof(f346,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f345,f224])).

fof(f345,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f255,f104])).

fof(f255,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f235,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f81,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f362,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f346,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f266,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f265,f105])).

fof(f265,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f257,f32])).

fof(f257,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f190,f67])).

fof(f190,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f189,f86])).

fof(f189,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f117])).

fof(f180,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f48,f175])).

fof(f434,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f432])).

fof(f432,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f429,f57])).

fof(f35,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f94,f32])).

fof(f94,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f1125,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f531,f1089])).

fof(f1089,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1081,f1088])).

fof(f1088,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1087,f744])).

fof(f744,plain,
    ( k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f743,f117])).

fof(f743,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f742,f86])).

fof(f742,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f739,f67])).

fof(f739,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f738])).

fof(f738,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f636,f665])).

fof(f665,plain,
    ( k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f662])).

fof(f662,plain,
    ( k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f598,f612])).

fof(f612,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f607,f572])).

fof(f572,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f535,f550])).

fof(f550,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f547,f530])).

fof(f530,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f34,f527])).

fof(f547,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(resolution,[],[f529,f70])).

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

fof(f529,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f527])).

fof(f535,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f92,f527])).

fof(f607,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f571,f68])).

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

fof(f571,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f534,f550])).

fof(f534,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f89,f527])).

fof(f598,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f542,f550])).

fof(f542,plain,(
    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f114,f527])).

fof(f636,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f635,f32])).

fof(f635,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f627,f105])).

fof(f627,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f48,f622])).

fof(f622,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f619])).

fof(f619,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f588,f581])).

fof(f581,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f576,f568])).

fof(f568,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f530,f550])).

fof(f576,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f567,f68])).

fof(f567,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f529,f550])).

fof(f588,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f539,f550])).

fof(f539,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f101,f527])).

fof(f1087,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1086,f86])).

fof(f1086,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1083,f117])).

fof(f1083,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f1075])).

fof(f1075,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f1072,f719])).

fof(f719,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f710])).

fof(f710,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f703,f638])).

fof(f638,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f637,f105])).

fof(f637,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f628,f32])).

fof(f628,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f49,f622])).

fof(f703,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f702,f117])).

fof(f702,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f701,f86])).

fof(f701,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f699,f67])).

fof(f699,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f698])).

fof(f698,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f632,f665])).

fof(f632,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f631,f32])).

fof(f631,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f625,f105])).

fof(f625,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f47,f622])).

fof(f1072,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1070,f695])).

fof(f695,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f691])).

fof(f691,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f688,f575])).

fof(f575,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK2,X1) = X1
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f545,f550])).

fof(f545,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(global_subsumption,[],[f31,f99])).

fof(f688,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f687,f86])).

fof(f687,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f686,f117])).

fof(f686,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f684,f67])).

fof(f684,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f683])).

fof(f683,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f630,f665])).

fof(f630,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f629,f105])).

fof(f629,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f624,f32])).

fof(f624,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f47,f622])).

fof(f1070,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1069])).

fof(f1069,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f735,f900])).

fof(f900,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f895,f696])).

fof(f696,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f688,f582])).

fof(f582,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f546,f550])).

fof(f546,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(global_subsumption,[],[f83,f99])).

fof(f895,plain,
    ( k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f809,f57])).

fof(f809,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f808,f744])).

fof(f808,plain,
    ( k1_xboole_0 = sK2
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f807,f86])).

fof(f807,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f806,f117])).

fof(f806,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f801])).

fof(f801,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f719,f696])).

fof(f735,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f734,f86])).

fof(f734,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f733,f117])).

fof(f733,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f730,f67])).

fof(f730,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f729])).

fof(f729,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f634,f665])).

fof(f634,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f633,f105])).

fof(f633,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f626,f32])).

fof(f626,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f48,f622])).

fof(f1081,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f1077])).

fof(f1077,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1072,f57])).

fof(f531,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f35,f527])).

fof(f593,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(superposition,[],[f531,f562])).

fof(f562,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f559,f535])).

fof(f559,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(resolution,[],[f534,f70])).

fof(f1220,plain,(
    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f536,f1214])).

fof(f1563,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1310,f1555])).

fof(f1555,plain,(
    k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1552,f1545])).

fof(f1545,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1544,f1497])).

fof(f1497,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1495,f1400])).

fof(f1400,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1386,f1314])).

fof(f1314,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | k1_funct_1(k1_xboole_0,X3) = X3 ) ),
    inference(backward_demodulation,[],[f1223,f1296])).

fof(f1223,plain,(
    ! [X3] :
      ( k1_funct_1(k1_xboole_0,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK1)) ) ),
    inference(backward_demodulation,[],[f545,f1214])).

fof(f1386,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1385,f117])).

fof(f1385,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1384,f86])).

fof(f1384,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1383,f67])).

fof(f1383,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1353,f1338])).

fof(f1338,plain,(
    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1303,f1337])).

fof(f1337,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1333,f1299])).

fof(f1299,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f535,f1296])).

fof(f1333,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f1298,f68])).

fof(f1298,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f534,f1296])).

fof(f1303,plain,(
    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f542,f1296])).

fof(f1353,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1352,f1215])).

fof(f1215,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f1214])).

fof(f1352,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1346,f1216])).

fof(f1216,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f105,f1214])).

fof(f1346,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f1321])).

fof(f1321,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1312,f1320])).

fof(f1320,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1315,f1309])).

fof(f1309,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1218,f1296])).

fof(f1218,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f530,f1214])).

fof(f1315,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f1308,f68])).

fof(f1308,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1217,f1296])).

fof(f1217,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f529,f1214])).

fof(f1312,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1221,f1296])).

fof(f1221,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f539,f1214])).

fof(f1495,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1476,f57])).

fof(f1476,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1475,f1407])).

fof(f1407,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1406,f86])).

fof(f1406,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1405,f117])).

fof(f1405,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1404,f67])).

fof(f1404,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f1355,f1338])).

fof(f1355,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f1354,f1216])).

fof(f1354,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f1347,f1215])).

fof(f1347,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f48,f1321])).

fof(f1475,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1474,f1216])).

fof(f1474,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1468,f1215])).

fof(f1468,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1401,f1400])).

fof(f1401,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f1376,f1381])).

fof(f1381,plain,
    ( r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1380,f86])).

fof(f1380,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1379,f117])).

fof(f1379,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1378,f67])).

fof(f1378,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f1351,f1338])).

fof(f1351,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f1350,f1216])).

fof(f1350,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f1345,f1215])).

fof(f1345,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f47,f1321])).

fof(f1376,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(subsumption_resolution,[],[f1375,f117])).

fof(f1375,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(subsumption_resolution,[],[f1366,f86])).

fof(f1366,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(superposition,[],[f49,f1338])).

fof(f1544,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) != k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f1412,f1520])).

fof(f1520,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1518,f1398])).

fof(f1398,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1386,f1305])).

fof(f1305,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(backward_demodulation,[],[f546,f1296])).

fof(f1518,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1473,f57])).

fof(f1473,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1472,f1407])).

fof(f1472,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1471,f1216])).

fof(f1471,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1467,f1215])).

fof(f1467,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1401,f1398])).

fof(f1412,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1411,f117])).

fof(f1411,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1410,f86])).

fof(f1410,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1409,f67])).

fof(f1409,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1357,f1338])).

fof(f1357,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1356,f1215])).

fof(f1356,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1348,f1216])).

fof(f1348,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f48,f1321])).

fof(f1552,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1550])).

fof(f1550,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1543,f57])).

fof(f1543,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1542,f1481])).

fof(f1481,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1477])).

fof(f1477,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1466,f1419])).

fof(f1419,plain,
    ( ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1390,f57])).

fof(f1390,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1381,f1314])).

fof(f1466,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1465,f1412])).

fof(f1465,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1464,f86])).

fof(f1464,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1458,f117])).

fof(f1458,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1396,f1390])).

fof(f1396,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
      | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ) ),
    inference(resolution,[],[f1386,f1359])).

fof(f1359,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f1358,f1216])).

fof(f1358,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f1349,f1215])).

fof(f1349,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f49,f1321])).

fof(f1542,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f1407,f1509])).

fof(f1509,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1507,f1388])).

fof(f1388,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1381,f1305])).

fof(f1507,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1463,f57])).

fof(f1463,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1462,f1412])).

fof(f1462,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1461,f86])).

fof(f1461,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1457,f117])).

fof(f1457,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1396,f1388])).

fof(f1310,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1219,f1296])).

fof(f1219,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f531,f1214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:47:20 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.46  % (3406)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (3413)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (3398)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (3412)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (3396)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (3418)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (3410)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (3408)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (3395)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (3403)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (3399)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (3394)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (3400)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.50/0.56  % (3394)Refutation not found, incomplete strategy% (3394)------------------------------
% 1.50/0.56  % (3394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (3394)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (3394)Memory used [KB]: 10618
% 1.50/0.56  % (3394)Time elapsed: 0.131 s
% 1.50/0.56  % (3394)------------------------------
% 1.50/0.56  % (3394)------------------------------
% 1.50/0.56  % (3416)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.50/0.57  % (3409)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.50/0.57  % (3407)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.50/0.57  % (3400)Refutation not found, incomplete strategy% (3400)------------------------------
% 1.50/0.57  % (3400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (3400)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (3400)Memory used [KB]: 10746
% 1.50/0.57  % (3400)Time elapsed: 0.087 s
% 1.50/0.57  % (3400)------------------------------
% 1.50/0.57  % (3400)------------------------------
% 1.50/0.57  % (3401)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.50/0.57  % (3417)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.50/0.58  % (3415)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.50/0.58  % (3414)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.78/0.58  % (3402)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.78/0.58  % (3401)Refutation not found, incomplete strategy% (3401)------------------------------
% 1.78/0.58  % (3401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.58  % (3401)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.58  
% 1.78/0.58  % (3401)Memory used [KB]: 1663
% 1.78/0.58  % (3401)Time elapsed: 0.151 s
% 1.78/0.58  % (3401)------------------------------
% 1.78/0.58  % (3401)------------------------------
% 1.78/0.63  % (3397)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.78/0.64  % (3399)Refutation found. Thanks to Tanya!
% 1.78/0.64  % SZS status Theorem for theBenchmark
% 1.78/0.64  % SZS output start Proof for theBenchmark
% 1.78/0.64  fof(f1591,plain,(
% 1.78/0.64    $false),
% 1.78/0.64    inference(subsumption_resolution,[],[f1563,f1311])).
% 1.78/0.64  fof(f1311,plain,(
% 1.78/0.64    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f1220,f1296])).
% 1.78/0.64  fof(f1296,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1224,f1220])).
% 1.78/0.64  fof(f1224,plain,(
% 1.78/0.64    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK1)),
% 1.78/0.64    inference(backward_demodulation,[],[f593,f1214])).
% 1.78/0.64  fof(f1214,plain,(
% 1.78/0.64    k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f1125,f536])).
% 1.78/0.64  fof(f536,plain,(
% 1.78/0.64    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2)),
% 1.78/0.64    inference(backward_demodulation,[],[f97,f527])).
% 1.78/0.64  fof(f527,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f451,f97])).
% 1.78/0.64  fof(f451,plain,(
% 1.78/0.64    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(superposition,[],[f35,f440])).
% 1.78/0.64  fof(f440,plain,(
% 1.78/0.64    sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f434,f439])).
% 1.78/0.64  fof(f439,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f438,f278])).
% 1.78/0.64  fof(f278,plain,(
% 1.78/0.64    k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f277,f32])).
% 1.78/0.64  fof(f32,plain,(
% 1.78/0.64    v1_funct_1(sK2)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f15,plain,(
% 1.78/0.64    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.64    inference(flattening,[],[f14])).
% 1.78/0.64  fof(f14,plain,(
% 1.78/0.64    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.78/0.64    inference(ennf_transformation,[],[f13])).
% 1.78/0.64  fof(f13,negated_conjecture,(
% 1.78/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.78/0.64    inference(negated_conjecture,[],[f12])).
% 1.78/0.64  fof(f12,conjecture,(
% 1.78/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 1.78/0.64  fof(f277,plain,(
% 1.78/0.64    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f269,f105])).
% 1.78/0.64  fof(f105,plain,(
% 1.78/0.64    v1_relat_1(sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f102,f53])).
% 1.78/0.64  fof(f53,plain,(
% 1.78/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f4])).
% 1.78/0.64  fof(f4,axiom,(
% 1.78/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.78/0.64  fof(f102,plain,(
% 1.78/0.64    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(sK2)),
% 1.78/0.64    inference(resolution,[],[f34,f58])).
% 1.78/0.64  fof(f58,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f28])).
% 1.78/0.64  fof(f28,plain,(
% 1.78/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.78/0.64    inference(ennf_transformation,[],[f3])).
% 1.78/0.64  fof(f3,axiom,(
% 1.78/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.78/0.64  fof(f34,plain,(
% 1.78/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f269,plain,(
% 1.78/0.64    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(resolution,[],[f192,f67])).
% 1.78/0.64  fof(f67,plain,(
% 1.78/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.78/0.64    inference(equality_resolution,[],[f55])).
% 1.78/0.64  fof(f55,plain,(
% 1.78/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.78/0.64    inference(cnf_transformation,[],[f1])).
% 1.78/0.64  fof(f1,axiom,(
% 1.78/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.64  fof(f192,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f191,f117])).
% 1.78/0.64  fof(f117,plain,(
% 1.78/0.64    v1_relat_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f115,f53])).
% 1.78/0.64  fof(f115,plain,(
% 1.78/0.64    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(resolution,[],[f92,f58])).
% 1.78/0.64  fof(f92,plain,(
% 1.78/0.64    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(subsumption_resolution,[],[f91,f38])).
% 1.78/0.64  fof(f38,plain,(
% 1.78/0.64    ~v2_struct_0(sK0)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f91,plain,(
% 1.78/0.64    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(subsumption_resolution,[],[f90,f40])).
% 1.78/0.64  fof(f40,plain,(
% 1.78/0.64    l1_pre_topc(sK0)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f90,plain,(
% 1.78/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(subsumption_resolution,[],[f78,f39])).
% 1.78/0.64  fof(f39,plain,(
% 1.78/0.64    v2_pre_topc(sK0)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f78,plain,(
% 1.78/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(resolution,[],[f37,f45])).
% 1.78/0.64  fof(f45,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f19])).
% 1.78/0.64  fof(f19,plain,(
% 1.78/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.64    inference(flattening,[],[f18])).
% 1.78/0.64  fof(f18,plain,(
% 1.78/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.64    inference(ennf_transformation,[],[f9])).
% 1.78/0.64  fof(f9,axiom,(
% 1.78/0.64    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 1.78/0.64  fof(f37,plain,(
% 1.78/0.64    m1_pre_topc(sK1,sK0)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f191,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f181,f86])).
% 1.78/0.64  fof(f86,plain,(
% 1.78/0.64    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f85,f38])).
% 1.78/0.64  fof(f85,plain,(
% 1.78/0.64    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f84,f40])).
% 1.78/0.64  fof(f84,plain,(
% 1.78/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f76,f39])).
% 1.78/0.64  fof(f76,plain,(
% 1.78/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(resolution,[],[f37,f43])).
% 1.78/0.64  fof(f43,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f19])).
% 1.78/0.64  fof(f181,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(superposition,[],[f48,f175])).
% 1.78/0.64  fof(f175,plain,(
% 1.78/0.64    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f172])).
% 1.78/0.64  fof(f172,plain,(
% 1.78/0.64    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(superposition,[],[f135,f139])).
% 1.78/0.64  fof(f139,plain,(
% 1.78/0.64    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f136])).
% 1.78/0.64  fof(f136,plain,(
% 1.78/0.64    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(superposition,[],[f110,f104])).
% 1.78/0.64  fof(f104,plain,(
% 1.78/0.64    u1_struct_0(sK1) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(backward_demodulation,[],[f95,f101])).
% 1.78/0.64  fof(f101,plain,(
% 1.78/0.64    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2)),
% 1.78/0.64    inference(resolution,[],[f34,f54])).
% 1.78/0.64  fof(f54,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f27])).
% 1.78/0.64  fof(f27,plain,(
% 1.78/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.64    inference(ennf_transformation,[],[f5])).
% 1.78/0.64  fof(f5,axiom,(
% 1.78/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.78/0.64  fof(f95,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f93,f34])).
% 1.78/0.64  fof(f93,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(resolution,[],[f33,f64])).
% 1.78/0.64  fof(f64,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f30])).
% 1.78/0.64  fof(f30,plain,(
% 1.78/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.64    inference(flattening,[],[f29])).
% 1.78/0.64  fof(f29,plain,(
% 1.78/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.64    inference(ennf_transformation,[],[f6])).
% 1.78/0.64  fof(f6,axiom,(
% 1.78/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.78/0.64  fof(f33,plain,(
% 1.78/0.64    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f110,plain,(
% 1.78/0.64    u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f108,f92])).
% 1.78/0.64  fof(f108,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.78/0.64    inference(resolution,[],[f89,f64])).
% 1.78/0.64  fof(f89,plain,(
% 1.78/0.64    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f88,f38])).
% 1.78/0.64  fof(f88,plain,(
% 1.78/0.64    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f87,f40])).
% 1.78/0.64  fof(f87,plain,(
% 1.78/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f77,f39])).
% 1.78/0.64  fof(f77,plain,(
% 1.78/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.78/0.64    inference(resolution,[],[f37,f44])).
% 1.78/0.64  fof(f44,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f19])).
% 1.78/0.64  fof(f135,plain,(
% 1.78/0.64    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(superposition,[],[f114,f104])).
% 1.78/0.64  fof(f114,plain,(
% 1.78/0.64    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(resolution,[],[f92,f54])).
% 1.78/0.64  fof(f48,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f23])).
% 1.78/0.64  fof(f23,plain,(
% 1.78/0.64    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.78/0.64    inference(flattening,[],[f22])).
% 1.78/0.64  fof(f22,plain,(
% 1.78/0.64    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.78/0.64    inference(ennf_transformation,[],[f8])).
% 1.78/0.64  fof(f8,axiom,(
% 1.78/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).
% 1.78/0.64  fof(f438,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f437,f86])).
% 1.78/0.64  fof(f437,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f436,f117])).
% 1.78/0.64  fof(f436,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f430])).
% 1.78/0.64  fof(f430,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(resolution,[],[f429,f250])).
% 1.78/0.64  fof(f250,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(sK2,X0) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f249,f105])).
% 1.78/0.64  fof(f249,plain,(
% 1.78/0.64    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f247,f32])).
% 1.78/0.64  fof(f247,plain,(
% 1.78/0.64    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0)) )),
% 1.78/0.64    inference(resolution,[],[f245,f49])).
% 1.78/0.64  fof(f49,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f23])).
% 1.78/0.64  fof(f245,plain,(
% 1.78/0.64    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f244,f32])).
% 1.78/0.64  fof(f244,plain,(
% 1.78/0.64    ~v1_funct_1(sK2) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f238,f105])).
% 1.78/0.64  fof(f238,plain,(
% 1.78/0.64    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(resolution,[],[f188,f67])).
% 1.78/0.64  fof(f188,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f187,f117])).
% 1.78/0.64  fof(f187,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f179,f86])).
% 1.78/0.64  fof(f179,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(superposition,[],[f47,f175])).
% 1.78/0.64  fof(f47,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r1_tarski(X0,X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f23])).
% 1.78/0.64  fof(f429,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f428,f281])).
% 1.78/0.64  fof(f281,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f280,f224])).
% 1.78/0.64  fof(f224,plain,(
% 1.78/0.64    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f223,f105])).
% 1.78/0.64  fof(f223,plain,(
% 1.78/0.64    ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f217,f32])).
% 1.78/0.64  fof(f217,plain,(
% 1.78/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(resolution,[],[f186,f67])).
% 1.78/0.64  fof(f186,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f185,f86])).
% 1.78/0.64  fof(f185,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f178,f117])).
% 1.78/0.64  fof(f178,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(superposition,[],[f47,f175])).
% 1.78/0.64  fof(f280,plain,(
% 1.78/0.64    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f279])).
% 1.78/0.64  fof(f279,plain,(
% 1.78/0.64    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(superposition,[],[f256,f104])).
% 1.78/0.64  fof(f256,plain,(
% 1.78/0.64    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(resolution,[],[f235,f31])).
% 1.78/0.64  fof(f31,plain,(
% 1.78/0.64    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f235,plain,(
% 1.78/0.64    m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f233])).
% 1.78/0.64  fof(f233,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(resolution,[],[f224,f125])).
% 1.78/0.64  fof(f125,plain,(
% 1.78/0.64    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(superposition,[],[f99,f104])).
% 1.78/0.64  fof(f99,plain,(
% 1.78/0.64    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.78/0.64    inference(resolution,[],[f79,f51])).
% 1.78/0.64  fof(f51,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f25])).
% 1.78/0.64  fof(f25,plain,(
% 1.78/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.78/0.64    inference(flattening,[],[f24])).
% 1.78/0.64  fof(f24,plain,(
% 1.78/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.78/0.64    inference(ennf_transformation,[],[f2])).
% 1.78/0.64  fof(f2,axiom,(
% 1.78/0.64    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.78/0.64  fof(f79,plain,(
% 1.78/0.64    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f74,f40])).
% 1.78/0.64  fof(f74,plain,(
% 1.78/0.64    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.64    inference(resolution,[],[f37,f52])).
% 1.78/0.64  fof(f52,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f26])).
% 1.78/0.64  fof(f26,plain,(
% 1.78/0.64    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.78/0.64    inference(ennf_transformation,[],[f10])).
% 1.78/0.64  fof(f10,axiom,(
% 1.78/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.78/0.64  fof(f428,plain,(
% 1.78/0.64    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f427])).
% 1.78/0.64  fof(f427,plain,(
% 1.78/0.64    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(superposition,[],[f266,f369])).
% 1.78/0.64  fof(f369,plain,(
% 1.78/0.64    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f362,f368])).
% 1.78/0.64  fof(f368,plain,(
% 1.78/0.64    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f367,f278])).
% 1.78/0.64  fof(f367,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f366,f86])).
% 1.78/0.64  fof(f366,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f365,f117])).
% 1.78/0.64  fof(f365,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f360])).
% 1.78/0.64  fof(f360,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(resolution,[],[f346,f250])).
% 1.78/0.64  fof(f346,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f345,f224])).
% 1.78/0.64  fof(f345,plain,(
% 1.78/0.64    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f344])).
% 1.78/0.64  fof(f344,plain,(
% 1.78/0.64    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(superposition,[],[f255,f104])).
% 1.78/0.64  fof(f255,plain,(
% 1.78/0.64    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(resolution,[],[f235,f83])).
% 1.78/0.64  fof(f83,plain,(
% 1.78/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f82,f38])).
% 1.78/0.64  fof(f82,plain,(
% 1.78/0.64    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f81,f36])).
% 1.78/0.64  fof(f36,plain,(
% 1.78/0.64    ~v2_struct_0(sK1)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f81,plain,(
% 1.78/0.64    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f80,f40])).
% 1.78/0.64  fof(f80,plain,(
% 1.78/0.64    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f75,f39])).
% 1.78/0.64  fof(f75,plain,(
% 1.78/0.64    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(resolution,[],[f37,f46])).
% 1.78/0.64  fof(f46,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 1.78/0.64    inference(cnf_transformation,[],[f21])).
% 1.78/0.64  fof(f21,plain,(
% 1.78/0.64    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.64    inference(flattening,[],[f20])).
% 1.78/0.64  fof(f20,plain,(
% 1.78/0.64    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.64    inference(ennf_transformation,[],[f11])).
% 1.78/0.64  fof(f11,axiom,(
% 1.78/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 1.78/0.64  fof(f362,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f346,f57])).
% 1.78/0.64  fof(f57,plain,(
% 1.78/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.78/0.64    inference(cnf_transformation,[],[f1])).
% 1.78/0.64  fof(f266,plain,(
% 1.78/0.64    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f265,f105])).
% 1.78/0.64  fof(f265,plain,(
% 1.78/0.64    ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f257,f32])).
% 1.78/0.64  fof(f257,plain,(
% 1.78/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.64    inference(resolution,[],[f190,f67])).
% 1.78/0.64  fof(f190,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f189,f86])).
% 1.78/0.64  fof(f189,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X2) | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f180,f117])).
% 1.78/0.64  fof(f180,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X2) | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 1.78/0.64    inference(superposition,[],[f48,f175])).
% 1.78/0.64  fof(f434,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f432])).
% 1.78/0.64  fof(f432,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f429,f57])).
% 1.78/0.64  fof(f35,plain,(
% 1.78/0.64    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(cnf_transformation,[],[f15])).
% 1.78/0.64  fof(f97,plain,(
% 1.78/0.64    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f96,f34])).
% 1.78/0.64  fof(f96,plain,(
% 1.78/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f94,f32])).
% 1.78/0.64  fof(f94,plain,(
% 1.78/0.64    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 1.78/0.64    inference(resolution,[],[f33,f73])).
% 1.78/0.64  fof(f73,plain,(
% 1.78/0.64    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f65])).
% 1.78/0.64  fof(f65,plain,(
% 1.78/0.64    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.78/0.64    inference(equality_resolution,[],[f41])).
% 1.78/0.64  fof(f41,plain,(
% 1.78/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f17])).
% 1.78/0.64  fof(f17,plain,(
% 1.78/0.64    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.78/0.64    inference(flattening,[],[f16])).
% 1.78/0.64  fof(f16,plain,(
% 1.78/0.64    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.78/0.64    inference(ennf_transformation,[],[f7])).
% 1.78/0.64  fof(f7,axiom,(
% 1.78/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.78/0.64  fof(f1125,plain,(
% 1.78/0.64    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f531,f1089])).
% 1.78/0.64  fof(f1089,plain,(
% 1.78/0.64    sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f1081,f1088])).
% 1.78/0.64  fof(f1088,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1087,f744])).
% 1.78/0.64  fof(f744,plain,(
% 1.78/0.64    k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f743,f117])).
% 1.78/0.64  fof(f743,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f742,f86])).
% 1.78/0.64  fof(f742,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f739,f67])).
% 1.78/0.64  fof(f739,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f738])).
% 1.78/0.64  fof(f738,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f636,f665])).
% 1.78/0.64  fof(f665,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f662])).
% 1.78/0.64  fof(f662,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f598,f612])).
% 1.78/0.64  fof(f612,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f607,f572])).
% 1.78/0.64  fof(f572,plain,(
% 1.78/0.64    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f535,f550])).
% 1.78/0.64  fof(f550,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f547,f530])).
% 1.78/0.64  fof(f530,plain,(
% 1.78/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 1.78/0.64    inference(backward_demodulation,[],[f34,f527])).
% 1.78/0.64  fof(f547,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 1.78/0.64    inference(resolution,[],[f529,f70])).
% 1.78/0.64  fof(f70,plain,(
% 1.78/0.64    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.78/0.64    inference(equality_resolution,[],[f60])).
% 1.78/0.64  fof(f60,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f30])).
% 1.78/0.64  fof(f529,plain,(
% 1.78/0.64    v1_funct_2(sK2,u1_struct_0(sK1),k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f33,f527])).
% 1.78/0.64  fof(f535,plain,(
% 1.78/0.64    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 1.78/0.64    inference(backward_demodulation,[],[f92,f527])).
% 1.78/0.64  fof(f607,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.64    inference(resolution,[],[f571,f68])).
% 1.78/0.64  fof(f68,plain,(
% 1.78/0.64    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.78/0.64    inference(equality_resolution,[],[f62])).
% 1.78/0.64  fof(f62,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f30])).
% 1.78/0.64  fof(f571,plain,(
% 1.78/0.64    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f534,f550])).
% 1.78/0.64  fof(f534,plain,(
% 1.78/0.64    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f89,f527])).
% 1.78/0.64  fof(f598,plain,(
% 1.78/0.64    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f542,f550])).
% 1.78/0.64  fof(f542,plain,(
% 1.78/0.64    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(backward_demodulation,[],[f114,f527])).
% 1.78/0.64  fof(f636,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f635,f32])).
% 1.78/0.64  fof(f635,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f627,f105])).
% 1.78/0.64  fof(f627,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f48,f622])).
% 1.78/0.64  fof(f622,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f619])).
% 1.78/0.64  fof(f619,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f588,f581])).
% 1.78/0.64  fof(f581,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f576,f568])).
% 1.78/0.64  fof(f568,plain,(
% 1.78/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f530,f550])).
% 1.78/0.64  fof(f576,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.64    inference(resolution,[],[f567,f68])).
% 1.78/0.64  fof(f567,plain,(
% 1.78/0.64    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f529,f550])).
% 1.78/0.64  fof(f588,plain,(
% 1.78/0.64    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f539,f550])).
% 1.78/0.64  fof(f539,plain,(
% 1.78/0.64    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,sK2)),
% 1.78/0.64    inference(backward_demodulation,[],[f101,f527])).
% 1.78/0.64  fof(f1087,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1086,f86])).
% 1.78/0.64  fof(f1086,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1083,f117])).
% 1.78/0.64  fof(f1083,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f1075])).
% 1.78/0.64  fof(f1075,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = sK2 | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(resolution,[],[f1072,f719])).
% 1.78/0.64  fof(f719,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(sK2,X0) | k1_xboole_0 = sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)) )),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f710])).
% 1.78/0.64  fof(f710,plain,(
% 1.78/0.64    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(resolution,[],[f703,f638])).
% 1.78/0.64  fof(f638,plain,(
% 1.78/0.64    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f637,f105])).
% 1.78/0.64  fof(f637,plain,(
% 1.78/0.64    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(sK2) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f628,f32])).
% 1.78/0.64  fof(f628,plain,(
% 1.78/0.64    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(sK2) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f49,f622])).
% 1.78/0.64  fof(f703,plain,(
% 1.78/0.64    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f702,f117])).
% 1.78/0.64  fof(f702,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f701,f86])).
% 1.78/0.64  fof(f701,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f699,f67])).
% 1.78/0.64  fof(f699,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f698])).
% 1.78/0.64  fof(f698,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f632,f665])).
% 1.78/0.64  fof(f632,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f631,f32])).
% 1.78/0.64  fof(f631,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f625,f105])).
% 1.78/0.64  fof(f625,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f47,f622])).
% 1.78/0.64  fof(f1072,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1070,f695])).
% 1.78/0.64  fof(f695,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f691])).
% 1.78/0.64  fof(f691,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(resolution,[],[f688,f575])).
% 1.78/0.64  fof(f575,plain,(
% 1.78/0.64    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK2,X1) = X1 | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f545,f550])).
% 1.78/0.64  fof(f545,plain,(
% 1.78/0.64    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 1.78/0.64    inference(global_subsumption,[],[f31,f99])).
% 1.78/0.64  fof(f688,plain,(
% 1.78/0.64    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f687,f86])).
% 1.78/0.64  fof(f687,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f686,f117])).
% 1.78/0.64  fof(f686,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f684,f67])).
% 1.78/0.64  fof(f684,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f683])).
% 1.78/0.64  fof(f683,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f630,f665])).
% 1.78/0.64  fof(f630,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f629,f105])).
% 1.78/0.64  fof(f629,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f624,f32])).
% 1.78/0.64  fof(f624,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f47,f622])).
% 1.78/0.64  fof(f1070,plain,(
% 1.78/0.64    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f1069])).
% 1.78/0.64  fof(f1069,plain,(
% 1.78/0.64    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(superposition,[],[f735,f900])).
% 1.78/0.64  fof(f900,plain,(
% 1.78/0.64    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f895,f696])).
% 1.78/0.64  fof(f696,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f690])).
% 1.78/0.64  fof(f690,plain,(
% 1.78/0.64    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(resolution,[],[f688,f582])).
% 1.78/0.64  fof(f582,plain,(
% 1.78/0.64    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f546,f550])).
% 1.78/0.64  fof(f546,plain,(
% 1.78/0.64    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(global_subsumption,[],[f83,f99])).
% 1.78/0.64  fof(f895,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f809,f57])).
% 1.78/0.64  fof(f809,plain,(
% 1.78/0.64    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f808,f744])).
% 1.78/0.64  fof(f808,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f807,f86])).
% 1.78/0.64  fof(f807,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f806,f117])).
% 1.78/0.64  fof(f806,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f801])).
% 1.78/0.64  fof(f801,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(resolution,[],[f719,f696])).
% 1.78/0.64  fof(f735,plain,(
% 1.78/0.64    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f734,f86])).
% 1.78/0.64  fof(f734,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f733,f117])).
% 1.78/0.64  fof(f733,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(subsumption_resolution,[],[f730,f67])).
% 1.78/0.64  fof(f730,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f729])).
% 1.78/0.64  fof(f729,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.78/0.64    inference(superposition,[],[f634,f665])).
% 1.78/0.64  fof(f634,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f633,f105])).
% 1.78/0.64  fof(f633,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f626,f32])).
% 1.78/0.64  fof(f626,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 1.78/0.64    inference(superposition,[],[f48,f622])).
% 1.78/0.64  fof(f1081,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f1077])).
% 1.78/0.64  fof(f1077,plain,(
% 1.78/0.64    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f1072,f57])).
% 1.78/0.64  fof(f531,plain,(
% 1.78/0.64    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),sK2)),
% 1.78/0.64    inference(backward_demodulation,[],[f35,f527])).
% 1.78/0.64  fof(f593,plain,(
% 1.78/0.64    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = u1_struct_0(sK1)),
% 1.78/0.64    inference(superposition,[],[f531,f562])).
% 1.78/0.64  fof(f562,plain,(
% 1.78/0.64    k1_xboole_0 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f559,f535])).
% 1.78/0.64  fof(f559,plain,(
% 1.78/0.64    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 1.78/0.64    inference(resolution,[],[f534,f70])).
% 1.78/0.64  fof(f1220,plain,(
% 1.78/0.64    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f536,f1214])).
% 1.78/0.64  fof(f1563,plain,(
% 1.78/0.64    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f1310,f1555])).
% 1.78/0.64  fof(f1555,plain,(
% 1.78/0.64    k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1552,f1545])).
% 1.78/0.64  fof(f1545,plain,(
% 1.78/0.64    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1544,f1497])).
% 1.78/0.64  fof(f1497,plain,(
% 1.78/0.64    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1495,f1400])).
% 1.78/0.64  fof(f1400,plain,(
% 1.78/0.64    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(resolution,[],[f1386,f1314])).
% 1.78/0.64  fof(f1314,plain,(
% 1.78/0.64    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k1_xboole_0,X3) = X3) )),
% 1.78/0.64    inference(backward_demodulation,[],[f1223,f1296])).
% 1.78/0.64  fof(f1223,plain,(
% 1.78/0.64    ( ! [X3] : (k1_funct_1(k1_xboole_0,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1))) )),
% 1.78/0.64    inference(backward_demodulation,[],[f545,f1214])).
% 1.78/0.64  fof(f1386,plain,(
% 1.78/0.64    r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1385,f117])).
% 1.78/0.64  fof(f1385,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1384,f86])).
% 1.78/0.64  fof(f1384,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1383,f67])).
% 1.78/0.64  fof(f1383,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(superposition,[],[f1353,f1338])).
% 1.78/0.64  fof(f1338,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(backward_demodulation,[],[f1303,f1337])).
% 1.78/0.64  fof(f1337,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1333,f1299])).
% 1.78/0.64  fof(f1299,plain,(
% 1.78/0.64    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.64    inference(backward_demodulation,[],[f535,f1296])).
% 1.78/0.64  fof(f1333,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.64    inference(resolution,[],[f1298,f68])).
% 1.78/0.64  fof(f1298,plain,(
% 1.78/0.64    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f534,f1296])).
% 1.78/0.64  fof(f1303,plain,(
% 1.78/0.64    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(backward_demodulation,[],[f542,f1296])).
% 1.78/0.64  fof(f1353,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1352,f1215])).
% 1.78/0.64  fof(f1215,plain,(
% 1.78/0.64    v1_funct_1(k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f32,f1214])).
% 1.78/0.64  fof(f1352,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1346,f1216])).
% 1.78/0.64  fof(f1216,plain,(
% 1.78/0.64    v1_relat_1(k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f105,f1214])).
% 1.78/0.64  fof(f1346,plain,(
% 1.78/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 1.78/0.64    inference(superposition,[],[f47,f1321])).
% 1.78/0.64  fof(f1321,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f1312,f1320])).
% 1.78/0.64  fof(f1320,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1315,f1309])).
% 1.78/0.64  fof(f1309,plain,(
% 1.78/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.64    inference(backward_demodulation,[],[f1218,f1296])).
% 1.78/0.64  fof(f1218,plain,(
% 1.78/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 1.78/0.64    inference(backward_demodulation,[],[f530,f1214])).
% 1.78/0.64  fof(f1315,plain,(
% 1.78/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.64    inference(resolution,[],[f1308,f68])).
% 1.78/0.64  fof(f1308,plain,(
% 1.78/0.64    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f1217,f1296])).
% 1.78/0.64  fof(f1217,plain,(
% 1.78/0.64    v1_funct_2(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f529,f1214])).
% 1.78/0.64  fof(f1312,plain,(
% 1.78/0.64    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f1221,f1296])).
% 1.78/0.64  fof(f1221,plain,(
% 1.78/0.64    k1_relat_1(k1_xboole_0) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),
% 1.78/0.64    inference(backward_demodulation,[],[f539,f1214])).
% 1.78/0.64  fof(f1495,plain,(
% 1.78/0.64    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f1476,f57])).
% 1.78/0.64  fof(f1476,plain,(
% 1.78/0.64    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1475,f1407])).
% 1.78/0.64  fof(f1407,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1406,f86])).
% 1.78/0.64  fof(f1406,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1405,f117])).
% 1.78/0.64  fof(f1405,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1404,f67])).
% 1.78/0.64  fof(f1404,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(superposition,[],[f1355,f1338])).
% 1.78/0.64  fof(f1355,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1354,f1216])).
% 1.78/0.64  fof(f1354,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1347,f1215])).
% 1.78/0.64  fof(f1347,plain,(
% 1.78/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 1.78/0.64    inference(superposition,[],[f48,f1321])).
% 1.78/0.64  fof(f1475,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1474,f1216])).
% 1.78/0.64  fof(f1474,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1468,f1215])).
% 1.78/0.64  fof(f1468,plain,(
% 1.78/0.64    ~v1_funct_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(resolution,[],[f1401,f1400])).
% 1.78/0.64  fof(f1401,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(X0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))) )),
% 1.78/0.64    inference(resolution,[],[f1376,f1381])).
% 1.78/0.64  fof(f1381,plain,(
% 1.78/0.64    r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1380,f86])).
% 1.78/0.64  fof(f1380,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1379,f117])).
% 1.78/0.64  fof(f1379,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1378,f67])).
% 1.78/0.64  fof(f1378,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 1.78/0.64    inference(superposition,[],[f1351,f1338])).
% 1.78/0.64  fof(f1351,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1350,f1216])).
% 1.78/0.64  fof(f1350,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1345,f1215])).
% 1.78/0.64  fof(f1345,plain,(
% 1.78/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.78/0.64    inference(superposition,[],[f47,f1321])).
% 1.78/0.64  fof(f1376,plain,(
% 1.78/0.64    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1375,f117])).
% 1.78/0.64  fof(f1375,plain,(
% 1.78/0.64    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1366,f86])).
% 1.78/0.64  fof(f1366,plain,(
% 1.78/0.64    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 1.78/0.64    inference(superposition,[],[f49,f1338])).
% 1.78/0.64  fof(f1544,plain,(
% 1.78/0.64    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) != k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(superposition,[],[f1412,f1520])).
% 1.78/0.64  fof(f1520,plain,(
% 1.78/0.64    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1518,f1398])).
% 1.78/0.64  fof(f1398,plain,(
% 1.78/0.64    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(resolution,[],[f1386,f1305])).
% 1.78/0.64  fof(f1305,plain,(
% 1.78/0.64    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 1.78/0.64    inference(backward_demodulation,[],[f546,f1296])).
% 1.78/0.64  fof(f1518,plain,(
% 1.78/0.64    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f1473,f57])).
% 1.78/0.64  fof(f1473,plain,(
% 1.78/0.64    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1472,f1407])).
% 1.78/0.64  fof(f1472,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1471,f1216])).
% 1.78/0.64  fof(f1471,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1467,f1215])).
% 1.78/0.64  fof(f1467,plain,(
% 1.78/0.64    ~v1_funct_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 1.78/0.64    inference(resolution,[],[f1401,f1398])).
% 1.78/0.64  fof(f1412,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1411,f117])).
% 1.78/0.64  fof(f1411,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1410,f86])).
% 1.78/0.64  fof(f1410,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1409,f67])).
% 1.78/0.64  fof(f1409,plain,(
% 1.78/0.64    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(superposition,[],[f1357,f1338])).
% 1.78/0.64  fof(f1357,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1356,f1215])).
% 1.78/0.64  fof(f1356,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f1348,f1216])).
% 1.78/0.64  fof(f1348,plain,(
% 1.78/0.64    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 1.78/0.64    inference(superposition,[],[f48,f1321])).
% 1.78/0.64  fof(f1552,plain,(
% 1.78/0.64    k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f1550])).
% 1.78/0.64  fof(f1550,plain,(
% 1.78/0.64    k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f1543,f57])).
% 1.78/0.64  fof(f1543,plain,(
% 1.78/0.64    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f1542,f1481])).
% 1.78/0.64  fof(f1481,plain,(
% 1.78/0.64    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f1477])).
% 1.78/0.64  fof(f1477,plain,(
% 1.78/0.64    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f1466,f1419])).
% 1.78/0.64  fof(f1419,plain,(
% 1.78/0.64    ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 1.78/0.64    inference(resolution,[],[f1390,f57])).
% 1.78/0.64  fof(f1390,plain,(
% 1.78/0.64    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(resolution,[],[f1381,f1314])).
% 1.78/0.64  fof(f1466,plain,(
% 1.78/0.64    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1465,f1412])).
% 1.78/0.64  fof(f1465,plain,(
% 1.78/0.64    k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1464,f86])).
% 1.78/0.64  fof(f1464,plain,(
% 1.78/0.64    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(subsumption_resolution,[],[f1458,f117])).
% 1.78/0.64  fof(f1458,plain,(
% 1.78/0.64    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 1.78/0.64    inference(resolution,[],[f1396,f1390])).
% 2.31/0.66  fof(f1396,plain,(
% 2.31/0.66    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)) )),
% 2.31/0.66    inference(resolution,[],[f1386,f1359])).
% 2.31/0.66  fof(f1359,plain,(
% 2.31/0.66    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 2.31/0.66    inference(subsumption_resolution,[],[f1358,f1216])).
% 2.31/0.66  fof(f1358,plain,(
% 2.31/0.66    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 2.31/0.66    inference(subsumption_resolution,[],[f1349,f1215])).
% 2.31/0.66  fof(f1349,plain,(
% 2.31/0.66    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 2.31/0.66    inference(superposition,[],[f49,f1321])).
% 2.31/0.66  fof(f1542,plain,(
% 2.31/0.66    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.31/0.66    inference(superposition,[],[f1407,f1509])).
% 2.31/0.66  fof(f1509,plain,(
% 2.31/0.66    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.31/0.66    inference(subsumption_resolution,[],[f1507,f1388])).
% 2.31/0.66  fof(f1388,plain,(
% 2.31/0.66    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.31/0.66    inference(resolution,[],[f1381,f1305])).
% 2.31/0.66  fof(f1507,plain,(
% 2.31/0.66    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.31/0.66    inference(resolution,[],[f1463,f57])).
% 2.31/0.66  fof(f1463,plain,(
% 2.31/0.66    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.31/0.66    inference(subsumption_resolution,[],[f1462,f1412])).
% 2.31/0.66  fof(f1462,plain,(
% 2.31/0.66    k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.31/0.66    inference(subsumption_resolution,[],[f1461,f86])).
% 2.31/0.66  fof(f1461,plain,(
% 2.31/0.66    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.31/0.66    inference(subsumption_resolution,[],[f1457,f117])).
% 2.31/0.66  fof(f1457,plain,(
% 2.31/0.66    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.31/0.66    inference(resolution,[],[f1396,f1388])).
% 2.31/0.66  fof(f1310,plain,(
% 2.31/0.66    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.31/0.66    inference(backward_demodulation,[],[f1219,f1296])).
% 2.31/0.66  fof(f1219,plain,(
% 2.31/0.66    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.31/0.66    inference(backward_demodulation,[],[f531,f1214])).
% 2.31/0.66  % SZS output end Proof for theBenchmark
% 2.31/0.66  % (3399)------------------------------
% 2.31/0.66  % (3399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.66  % (3399)Termination reason: Refutation
% 2.31/0.66  
% 2.31/0.66  % (3399)Memory used [KB]: 6524
% 2.31/0.66  % (3399)Time elapsed: 0.200 s
% 2.31/0.66  % (3399)------------------------------
% 2.31/0.66  % (3399)------------------------------
% 2.31/0.66  % (3393)Success in time 0.303 s
% 2.31/0.66  % (3411)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
%------------------------------------------------------------------------------
