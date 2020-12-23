%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1331+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:45 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 106 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   18
%              Number of atoms          :  185 ( 483 expanded)
%              Number of equality atoms :   39 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f105])).

fof(f105,plain,(
    k1_xboole_0 = u1_struct_0(sK1) ),
    inference(resolution,[],[f104,f29])).

fof(f29,plain,(
    ~ m1_subset_1(k9_relat_1(k3_funct_3(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => m1_subset_1(k9_relat_1(k3_funct_3(X2),X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_2)).

fof(f104,plain,(
    ! [X4] :
      ( m1_subset_1(k9_relat_1(k3_funct_3(sK2),X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 = u1_struct_0(sK1) ) ),
    inference(resolution,[],[f101,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f101,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k3_funct_3(sK2),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = u1_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f98,f78])).

fof(f78,plain,(
    v1_relat_1(k3_funct_3(sK2)) ),
    inference(resolution,[],[f65,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(k3_funct_3(sK2)) ) ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f58,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k3_funct_3(sK2)) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k3_funct_3(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = u1_struct_0(sK1)
      | r1_tarski(k9_relat_1(k3_funct_3(sK2),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_relat_1(k3_funct_3(sK2)) ) ),
    inference(resolution,[],[f94,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(k3_funct_3(sK2)))
      | k1_xboole_0 = u1_struct_0(sK1)
      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f92,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f92,plain,
    ( r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(resolution,[],[f91,f32])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = u1_struct_0(sK1)
      | r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f90,f44])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,
    ( r1_tarski(k2_relat_1(k3_funct_3(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(superposition,[],[f38,f84])).

fof(f84,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(superposition,[],[f68,f71])).

fof(f71,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f67,f32])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f31,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_tarski(k2_relat_1(k3_funct_3(X0)),k1_zfmisc_1(k1_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_3)).

fof(f63,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f62,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f34,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
