%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 224 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   20
%              Number of atoms          :  341 (1890 expanded)
%              Number of equality atoms :   54 ( 171 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f332,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f332,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f127,f328])).

fof(f328,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f326,f172])).

fof(f172,plain,(
    k9_relat_1(sK3,sK4) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(resolution,[],[f122,f142])).

fof(f142,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
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
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(X4,u1_struct_0(X2))
                         => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

fof(f122,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k9_relat_1(k7_relat_1(X3,u1_struct_0(sK2)),sK4) = k9_relat_1(X3,sK4) ) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f32,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f326,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f325,f219])).

fof(f219,plain,(
    ! [X0] :
      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X0) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X0)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f202,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f202,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f174,f152])).

fof(f152,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f151,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f151,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f148,f38])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f148,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f111,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | ~ m1_pre_topc(sK2,X2)
      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f110,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_pre_topc(sK2,X2)
      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_pre_topc(sK2,X2)
      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f174,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,u1_struct_0(sK1))
      | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(backward_demodulation,[],[f135,f173])).

fof(f173,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) ),
    inference(resolution,[],[f69,f36])).

fof(f69,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k2_partfun1(X7,X8,sK3,X9) = k7_relat_1(sK3,X9) ) ),
    inference(resolution,[],[f34,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f135,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,u1_struct_0(sK1))
      | k1_xboole_0 = u1_struct_0(sK0)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f134,f36])).

fof(f134,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tarski(X2,u1_struct_0(sK1))
      | k1_xboole_0 = u1_struct_0(sK0)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f131,f34])).

fof(f131,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tarski(X2,u1_struct_0(sK1))
      | k1_xboole_0 = u1_struct_0(sK0)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f35,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f35,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f325,plain,(
    k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(backward_demodulation,[],[f143,f324])).

fof(f324,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f323,f173])).

fof(f323,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f322,f36])).

fof(f322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f317,f34])).

fof(f317,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f243,f35])).

fof(f243,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f242,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f242,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f239,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X1,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f118,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,(
    ! [X6,X5] :
      ( ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
      | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,(
    ! [X6,X5] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
      | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f116,plain,(
    ! [X6,X5] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
      | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    ! [X6,X5] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
      | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f143,plain,(
    k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f33,f141])).

fof(f141,plain,(
    ! [X0] : k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f36,f54])).

fof(f33,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f126,f44])).

fof(f126,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f91,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:26:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (8782)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (8782)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f339,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f332,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f332,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(backward_demodulation,[],[f127,f328])).
% 0.22/0.47  fof(f328,plain,(
% 0.22/0.47    k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f326,f172])).
% 0.22/0.47  fof(f172,plain,(
% 0.22/0.47    k9_relat_1(sK3,sK4) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.47    inference(resolution,[],[f122,f142])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    v1_relat_1(sK3)),
% 0.22/0.47    inference(resolution,[],[f36,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f12])).
% 0.22/0.47  fof(f12,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    ( ! [X3] : (~v1_relat_1(X3) | k9_relat_1(k7_relat_1(X3,u1_struct_0(sK2)),sK4) = k9_relat_1(X3,sK4)) )),
% 0.22/0.47    inference(resolution,[],[f32,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    r1_tarski(sK4,u1_struct_0(sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f326,plain,(
% 0.22/0.47    k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.47    inference(superposition,[],[f325,f219])).
% 0.22/0.47  fof(f219,plain,(
% 0.22/0.47    ( ! [X0] : (k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X0) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X0) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.47    inference(resolution,[],[f202,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.47  fof(f202,plain,(
% 0.22/0.47    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.47    inference(resolution,[],[f174,f152])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.47    inference(subsumption_resolution,[],[f151,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    l1_pre_topc(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f148,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    m1_pre_topc(sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    ~m1_pre_topc(sK2,sK1) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.47    inference(resolution,[],[f111,f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ( ! [X2] : (~m1_pre_topc(X2,sK1) | ~m1_pre_topc(sK2,X2) | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f110,f41])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    ( ! [X2] : (~l1_pre_topc(sK1) | ~m1_pre_topc(X2,sK1) | ~m1_pre_topc(sK2,X2) | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f104,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    v2_pre_topc(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ( ! [X2] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X2,sK1) | ~m1_pre_topc(sK2,X2) | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2))) )),
% 0.22/0.47    inference(resolution,[],[f38,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.47  fof(f174,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK1)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0)))) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f135,f173])).
% 0.22/0.47  fof(f173,plain,(
% 0.22/0.47    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) )),
% 0.22/0.47    inference(resolution,[],[f69,f36])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X8,X7,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k2_partfun1(X7,X8,sK3,X9) = k7_relat_1(sK3,X9)) )),
% 0.22/0.47    inference(resolution,[],[f34,f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.47    inference(flattening,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    v1_funct_1(sK3)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK0) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f134,f36])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    ( ! [X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK0) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f131,f34])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    ( ! [X2] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK0) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK0))))) )),
% 0.22/0.47    inference(resolution,[],[f35,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.47    inference(flattening,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f325,plain,(
% 0.22/0.48    k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.48    inference(backward_demodulation,[],[f143,f324])).
% 0.22/0.48  fof(f324,plain,(
% 0.22/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f323,f173])).
% 0.22/0.48  fof(f323,plain,(
% 0.22/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f322,f36])).
% 0.22/0.48  fof(f322,plain,(
% 0.22/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f317,f34])).
% 0.22/0.48  fof(f317,plain,(
% 0.22/0.48    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 0.22/0.48    inference(resolution,[],[f243,f35])).
% 0.22/0.48  fof(f243,plain,(
% 0.22/0.48    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X1,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f242,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f242,plain,(
% 0.22/0.48    ( ! [X1] : (~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X1,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f239,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f239,plain,(
% 0.22/0.48    ( ! [X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X1,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(resolution,[],[f118,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X6,X5] : (~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X5) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5)))) | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f41])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X6,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5)))) | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f116,f40])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ( ! [X6,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5)))) | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f107,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~v2_struct_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X6,X5] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(sK1),u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5)))) | k2_tmap_1(sK1,X5,X6,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X5),X6,u1_struct_0(sK2))) )),
% 0.22/0.48    inference(resolution,[],[f38,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4)),
% 0.22/0.48    inference(backward_demodulation,[],[f33,f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.22/0.48    inference(resolution,[],[f36,f54])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f126,f44])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f91,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.48    inference(resolution,[],[f42,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (8782)------------------------------
% 0.22/0.48  % (8782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8782)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (8782)Memory used [KB]: 1791
% 0.22/0.48  % (8782)Time elapsed: 0.016 s
% 0.22/0.48  % (8782)------------------------------
% 0.22/0.48  % (8782)------------------------------
% 0.22/0.48  % (8766)Success in time 0.114 s
%------------------------------------------------------------------------------
