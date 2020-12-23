%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 417 expanded)
%              Number of leaves         :   18 (  80 expanded)
%              Depth                    :   28
%              Number of atoms          :  459 (2475 expanded)
%              Number of equality atoms :  105 ( 532 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1389,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1265,f120])).

fof(f120,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f116,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f84,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1265,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f66,f1261])).

fof(f1261,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1259,f59])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f1259,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1173,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1173,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1096,f165])).

fof(f165,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f164,f64])).

fof(f64,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f164,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f160,f66])).

fof(f160,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f111,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f76,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f1096,plain,
    ( v1_xboole_0(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1095,f120])).

fof(f1095,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK3) ),
    inference(forward_demodulation,[],[f1083,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1083,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK3) ),
    inference(duplicate_literal_removal,[],[f1012])).

fof(f1012,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f338,f991])).

fof(f991,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f989,f59])).

fof(f989,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f742,f70])).

fof(f742,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f738,f401])).

fof(f401,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f60,f400])).

fof(f400,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f399,f62])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f399,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f398,f61])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f398,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f396,f152])).

fof(f152,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f145,f149])).

fof(f149,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f88,f65])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f145,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f58,f139])).

fof(f139,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f87,f62])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f58,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f396,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[],[f276,f139])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f275,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f274,f66])).

fof(f274,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f273,f65])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f270,f64])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(superposition,[],[f205,f149])).

fof(f205,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) ) ),
    inference(subsumption_resolution,[],[f202,f59])).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | v1_xboole_0(X1)
      | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) ) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f60,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f738,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1)
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f499,f208])).

fof(f208,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f207,f61])).

fof(f207,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f206,f129])).

fof(f129,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f86,f62])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f206,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(resolution,[],[f133,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f133,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(resolution,[],[f89,f62])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f499,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | k1_xboole_0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f343,f126])).

fof(f126,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f75,f57])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f343,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = k1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f342,f251])).

fof(f251,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f191,f152])).

fof(f191,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | k1_xboole_0 = sK2
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(forward_demodulation,[],[f190,f149])).

fof(f190,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f189,f63])).

fof(f189,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f184,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(resolution,[],[f100,f65])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f342,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f334,f63])).

fof(f334,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f252,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f252,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f200,f152])).

fof(f200,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | k1_xboole_0 = sK2
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(forward_demodulation,[],[f199,f149])).

fof(f199,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f198,f63])).

fof(f198,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f193,f64])).

fof(f193,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(resolution,[],[f101,f65])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f338,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_relat_1(sK4)))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f252,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (18967)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.45  % (18959)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (18961)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (18969)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (18957)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (18960)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (18962)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (18972)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (18955)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (18953)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (18958)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (18956)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (18965)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (18963)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (18964)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (18954)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (18966)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (18971)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (18972)Refutation not found, incomplete strategy% (18972)------------------------------
% 0.20/0.52  % (18972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18972)Memory used [KB]: 10618
% 0.20/0.52  % (18972)Time elapsed: 0.115 s
% 0.20/0.52  % (18972)------------------------------
% 0.20/0.52  % (18972)------------------------------
% 0.20/0.52  % (18952)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (18953)Refutation not found, incomplete strategy% (18953)------------------------------
% 0.20/0.52  % (18953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18953)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18953)Memory used [KB]: 10746
% 0.20/0.52  % (18953)Time elapsed: 0.115 s
% 0.20/0.52  % (18953)------------------------------
% 0.20/0.52  % (18953)------------------------------
% 0.20/0.52  % (18955)Refutation not found, incomplete strategy% (18955)------------------------------
% 0.20/0.52  % (18955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18955)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18955)Memory used [KB]: 11001
% 0.20/0.52  % (18955)Time elapsed: 0.126 s
% 0.20/0.52  % (18955)------------------------------
% 0.20/0.52  % (18955)------------------------------
% 0.20/0.53  % (18970)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (18965)Refutation not found, incomplete strategy% (18965)------------------------------
% 0.20/0.53  % (18965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18965)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18965)Memory used [KB]: 1791
% 0.20/0.53  % (18965)Time elapsed: 0.112 s
% 0.20/0.53  % (18965)------------------------------
% 0.20/0.53  % (18965)------------------------------
% 0.20/0.53  % (18968)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.58  % (18969)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1389,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(subsumption_resolution,[],[f1265,f120])).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    v1_xboole_0(k1_xboole_0)),
% 0.20/0.58    inference(resolution,[],[f116,f72])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(resolution,[],[f84,f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.58  fof(f1265,plain,(
% 0.20/0.58    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.58    inference(backward_demodulation,[],[f66,f1261])).
% 0.20/0.58  fof(f1261,plain,(
% 0.20/0.58    k1_xboole_0 = sK2),
% 0.20/0.58    inference(subsumption_resolution,[],[f1259,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    k1_xboole_0 != sK1),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.20/0.58    inference(flattening,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.20/0.58    inference(ennf_transformation,[],[f25])).
% 0.20/0.58  fof(f25,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.58    inference(negated_conjecture,[],[f24])).
% 0.20/0.58  fof(f24,conjecture,(
% 0.20/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.20/0.58  fof(f1259,plain,(
% 0.20/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.58    inference(resolution,[],[f1173,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.58  fof(f1173,plain,(
% 0.20/0.58    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 0.20/0.58    inference(resolution,[],[f1096,f165])).
% 0.20/0.58  fof(f165,plain,(
% 0.20/0.58    ~v1_xboole_0(sK3) | v1_xboole_0(sK1)),
% 0.20/0.58    inference(subsumption_resolution,[],[f164,f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f164,plain,(
% 0.20/0.58    v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_xboole_0(sK3)),
% 0.20/0.58    inference(subsumption_resolution,[],[f160,f66])).
% 0.20/0.58  fof(f160,plain,(
% 0.20/0.58    v1_xboole_0(sK2) | v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_xboole_0(sK3)),
% 0.20/0.58    inference(resolution,[],[f111,f65])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f76,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f18])).
% 0.20/0.58  fof(f18,axiom,(
% 0.20/0.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 0.20/0.58  fof(f1096,plain,(
% 0.20/0.58    v1_xboole_0(sK3) | k1_xboole_0 = sK2),
% 0.20/0.58    inference(subsumption_resolution,[],[f1095,f120])).
% 0.20/0.58  fof(f1095,plain,(
% 0.20/0.58    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | v1_xboole_0(sK3)),
% 0.20/0.58    inference(forward_demodulation,[],[f1083,f102])).
% 0.20/0.58  fof(f102,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f83])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.58  fof(f1083,plain,(
% 0.20/0.58    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) | k1_xboole_0 = sK2 | v1_xboole_0(sK3)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f1012])).
% 0.20/0.58  fof(f1012,plain,(
% 0.20/0.58    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) | k1_xboole_0 = sK2 | v1_xboole_0(sK3) | k1_xboole_0 = sK2),
% 0.20/0.58    inference(superposition,[],[f338,f991])).
% 0.20/0.58  fof(f991,plain,(
% 0.20/0.58    k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.20/0.58    inference(subsumption_resolution,[],[f989,f59])).
% 0.20/0.58  fof(f989,plain,(
% 0.20/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK1),
% 0.20/0.58    inference(resolution,[],[f742,f70])).
% 0.20/0.58  fof(f742,plain,(
% 0.20/0.58    v1_xboole_0(sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = k1_relat_1(sK4)),
% 0.20/0.58    inference(subsumption_resolution,[],[f738,f401])).
% 0.20/0.58  fof(f401,plain,(
% 0.20/0.58    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(backward_demodulation,[],[f60,f400])).
% 0.20/0.58  fof(f400,plain,(
% 0.20/0.58    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(subsumption_resolution,[],[f399,f62])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f399,plain,(
% 0.20/0.58    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(subsumption_resolution,[],[f398,f61])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    v1_funct_1(sK4)),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f398,plain,(
% 0.20/0.58    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(subsumption_resolution,[],[f396,f152])).
% 0.20/0.58  fof(f152,plain,(
% 0.20/0.58    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.20/0.58    inference(backward_demodulation,[],[f145,f149])).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.20/0.58    inference(resolution,[],[f88,f65])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.58  fof(f145,plain,(
% 0.20/0.58    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.20/0.58    inference(backward_demodulation,[],[f58,f139])).
% 0.20/0.58  fof(f139,plain,(
% 0.20/0.58    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.20/0.58    inference(resolution,[],[f87,f62])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f396,plain,(
% 0.20/0.58    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(superposition,[],[f276,f139])).
% 0.20/0.58  fof(f276,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f275,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    v1_funct_1(sK3)),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f275,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f274,f66])).
% 0.20/0.58  fof(f274,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f273,f65])).
% 0.20/0.58  fof(f273,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f270,f64])).
% 0.20/0.58  fof(f270,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.20/0.58    inference(superposition,[],[f205,f149])).
% 0.20/0.58  fof(f205,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f202,f59])).
% 0.20/0.58  fof(f202,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) )),
% 0.20/0.58    inference(resolution,[],[f85,f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    m1_subset_1(sK5,sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.20/0.58    inference(flattening,[],[f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.20/0.58    inference(ennf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f738,plain,(
% 0.20/0.58    k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2 | v1_xboole_0(sK1) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.58    inference(resolution,[],[f499,f208])).
% 0.20/0.58  fof(f208,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f207,f61])).
% 0.20/0.58  fof(f207,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f206,f129])).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    v1_relat_1(sK4)),
% 0.20/0.58    inference(resolution,[],[f86,f62])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.58  fof(f206,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.20/0.58    inference(resolution,[],[f133,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.58    inference(flattening,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,axiom,(
% 0.20/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.58  fof(f133,plain,(
% 0.20/0.58    v5_relat_1(sK4,sK0)),
% 0.20/0.58    inference(resolution,[],[f89,f62])).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.58    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.58  fof(f499,plain,(
% 0.20/0.58    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.20/0.58    inference(resolution,[],[f343,f126])).
% 0.20/0.58  fof(f126,plain,(
% 0.20/0.58    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 0.20/0.58    inference(resolution,[],[f75,f57])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.58    inference(flattening,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.58  fof(f343,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f342,f251])).
% 0.20/0.58  fof(f251,plain,(
% 0.20/0.58    v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | k1_xboole_0 = sK2),
% 0.20/0.58    inference(resolution,[],[f191,f152])).
% 0.20/0.58  fof(f191,plain,(
% 0.20/0.58    ( ! [X1] : (~r1_tarski(k2_relat_1(sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f190,f149])).
% 0.20/0.58  fof(f190,plain,(
% 0.20/0.58    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f189,f63])).
% 0.20/0.58  fof(f189,plain,(
% 0.20/0.58    ( ! [X1] : (~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f184,f64])).
% 0.20/0.58  fof(f184,plain,(
% 0.20/0.58    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) )),
% 0.20/0.58    inference(resolution,[],[f100,f65])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.58    inference(flattening,[],[f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.58    inference(ennf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.20/0.58  fof(f342,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f334,f63])).
% 0.20/0.58  fof(f334,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) )),
% 0.20/0.58    inference(resolution,[],[f252,f97])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.58    inference(flattening,[],[f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.58    inference(ennf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.58  fof(f252,plain,(
% 0.20/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | k1_xboole_0 = sK2),
% 0.20/0.58    inference(resolution,[],[f200,f152])).
% 0.20/0.58  fof(f200,plain,(
% 0.20/0.58    ( ! [X1] : (~r1_tarski(k2_relat_1(sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f199,f149])).
% 0.20/0.58  fof(f199,plain,(
% 0.20/0.58    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f198,f63])).
% 0.20/0.58  fof(f198,plain,(
% 0.20/0.58    ( ! [X1] : (~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f193,f64])).
% 0.20/0.58  fof(f193,plain,(
% 0.20/0.58    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.20/0.58    inference(resolution,[],[f101,f65])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f56])).
% 0.20/0.58  fof(f338,plain,(
% 0.20/0.58    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_relat_1(sK4))) | k1_xboole_0 = sK2 | v1_xboole_0(sK3)),
% 0.20/0.58    inference(resolution,[],[f252,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ~v1_xboole_0(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (18969)------------------------------
% 0.20/0.58  % (18969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (18969)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (18969)Memory used [KB]: 3198
% 0.20/0.58  % (18969)Time elapsed: 0.158 s
% 0.20/0.58  % (18969)------------------------------
% 0.20/0.58  % (18969)------------------------------
% 0.20/0.58  % (18951)Success in time 0.228 s
%------------------------------------------------------------------------------
