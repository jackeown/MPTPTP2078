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
% DateTime   : Thu Dec  3 13:07:46 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 423 expanded)
%              Number of leaves         :   15 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  354 (2366 expanded)
%              Number of equality atoms :   87 ( 495 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f947,plain,(
    $false ),
    inference(global_subsumption,[],[f39,f946])).

fof(f946,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f938,f747])).

fof(f747,plain,(
    k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f691,f687])).

fof(f687,plain,(
    k1_xboole_0 = k9_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f129,f43,f99,f357,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP10(sK9(X0,X1,X2),X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f357,plain,(
    ! [X0,X1] : ~ sP10(X0,k9_relat_1(sK3,k1_xboole_0),X1) ),
    inference(unit_resulting_resolution,[],[f320,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK11(X0,X1,X3),X1)
      | ~ sP10(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f320,plain,(
    ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK3,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f129,f224,f43,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP10(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP10(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f224,plain,(
    ! [X0,X1] : ~ sP10(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f99,f57])).

fof(f99,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f47,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f129,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f45,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

% (28901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f691,plain,(
    k9_relat_1(sK3,k1_xboole_0) = k9_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f129,f43,f320,f357,f61])).

fof(f938,plain,(
    sK1 = k9_relat_1(sK3,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f129,f43,f224,f908,f61])).

fof(f908,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f901,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f901,plain,(
    v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f103,f865])).

fof(f865,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f46,f860])).

fof(f860,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f852,f106])).

fof(f106,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f852,plain,
    ( ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f847,f645])).

fof(f645,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f44,f644])).

fof(f644,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(forward_demodulation,[],[f642,f302])).

fof(f302,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f45,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f642,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f847,plain,(
    ~ r2_hidden(sK5,k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f841,f85])).

fof(f85,plain,(
    ! [X0,X3] :
      ( sP7(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f841,plain,(
    ~ sP7(k1_funct_1(sK3,sK5),sK3) ),
    inference(unit_resulting_resolution,[],[f838,f657])).

fof(f657,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK4))
      | ~ sP7(X0,sK3) ) ),
    inference(global_subsumption,[],[f43,f129,f653])).

fof(f653,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK3)
      | ~ sP7(X0,sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f307,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP7(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f307,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK3))
      | r2_hidden(X2,k1_relat_1(sK4)) ) ),
    inference(backward_demodulation,[],[f290,f301])).

fof(f301,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f42,f74])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f290,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK3))
      | r2_hidden(X2,k1_relset_1(sK2,sK0,sK4)) ) ),
    inference(backward_demodulation,[],[f169,f284])).

fof(f284,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f169,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relset_1(sK1,sK2,sK3))
      | r2_hidden(X2,k1_relset_1(sK2,sK0,sK4)) ) ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f838,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f128,f41,f196,f823,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f823,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(global_subsumption,[],[f46,f45,f44,f43,f42,f41,f39,f37,f309,f822])).

fof(f822,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2) ),
    inference(forward_demodulation,[],[f821,f284])).

fof(f821,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2) ),
    inference(forward_demodulation,[],[f816,f301])).

fof(f816,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f40,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f40,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f309,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f288,f301])).

fof(f288,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(backward_demodulation,[],[f38,f284])).

fof(f196,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(unit_resulting_resolution,[],[f42,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f42,f72])).

fof(f46,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 12:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (28930)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (28914)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (28908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (28909)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.06/0.51  % (28905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.06/0.51  % (28915)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.06/0.51  % (28925)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.06/0.52  % (28917)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.06/0.52  % (28924)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.06/0.52  % (28923)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.06/0.52  % (28929)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.06/0.53  % (28926)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.06/0.53  % (28921)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.53  % (28907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.53  % (28904)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (28916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.53  % (28913)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (28910)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.53  % (28918)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.53  % (28902)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (28928)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.54  % (28920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.54  % (28927)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.26/0.54  % (28922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.54  % (28906)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.54  % (28919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.26/0.55  % (28918)Refutation not found, incomplete strategy% (28918)------------------------------
% 1.26/0.55  % (28918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (28918)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (28918)Memory used [KB]: 10746
% 1.26/0.55  % (28918)Time elapsed: 0.130 s
% 1.26/0.55  % (28918)------------------------------
% 1.26/0.55  % (28918)------------------------------
% 1.26/0.55  % (28912)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.55  % (28903)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.56  % (28925)Refutation found. Thanks to Tanya!
% 1.26/0.56  % SZS status Theorem for theBenchmark
% 1.26/0.56  % (28911)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.56  % SZS output start Proof for theBenchmark
% 1.26/0.56  fof(f947,plain,(
% 1.26/0.56    $false),
% 1.26/0.56    inference(global_subsumption,[],[f39,f946])).
% 1.26/0.56  fof(f946,plain,(
% 1.26/0.56    k1_xboole_0 = sK1),
% 1.26/0.56    inference(forward_demodulation,[],[f938,f747])).
% 1.26/0.56  fof(f747,plain,(
% 1.26/0.56    k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0)),
% 1.26/0.56    inference(backward_demodulation,[],[f691,f687])).
% 1.26/0.56  fof(f687,plain,(
% 1.26/0.56    k1_xboole_0 = k9_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0))),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f129,f43,f99,f357,f61])).
% 1.26/0.56  fof(f61,plain,(
% 1.26/0.56    ( ! [X2,X0,X1] : (sP10(sK9(X0,X1,X2),X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK9(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2) )),
% 1.26/0.56    inference(cnf_transformation,[],[f22])).
% 1.26/0.56  fof(f22,plain,(
% 1.26/0.56    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.56    inference(flattening,[],[f21])).
% 1.26/0.56  fof(f21,plain,(
% 1.26/0.56    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.56    inference(ennf_transformation,[],[f5])).
% 1.26/0.56  fof(f5,axiom,(
% 1.26/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.26/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.26/0.56  fof(f357,plain,(
% 1.26/0.56    ( ! [X0,X1] : (~sP10(X0,k9_relat_1(sK3,k1_xboole_0),X1)) )),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f320,f57])).
% 1.26/0.56  fof(f57,plain,(
% 1.26/0.56    ( ! [X0,X3,X1] : (r2_hidden(sK11(X0,X1,X3),X1) | ~sP10(X3,X1,X0)) )),
% 1.26/0.56    inference(cnf_transformation,[],[f22])).
% 1.26/0.56  fof(f320,plain,(
% 1.26/0.56    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,k1_xboole_0))) )),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f129,f224,f43,f86])).
% 1.26/0.56  fof(f86,plain,(
% 1.26/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | sP10(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.26/0.56    inference(equality_resolution,[],[f60])).
% 1.26/0.56  fof(f60,plain,(
% 1.26/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP10(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.26/0.56    inference(cnf_transformation,[],[f22])).
% 1.26/0.56  fof(f224,plain,(
% 1.26/0.56    ( ! [X0,X1] : (~sP10(X0,k1_xboole_0,X1)) )),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f99,f57])).
% 1.26/0.56  fof(f99,plain,(
% 1.26/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f47,f70])).
% 1.26/0.56  fof(f70,plain,(
% 1.26/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.26/0.56    inference(cnf_transformation,[],[f28])).
% 1.26/0.56  fof(f28,plain,(
% 1.26/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.26/0.56    inference(ennf_transformation,[],[f7])).
% 1.26/0.56  fof(f7,axiom,(
% 1.26/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.26/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.26/0.56  fof(f47,plain,(
% 1.26/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.26/0.56    inference(cnf_transformation,[],[f3])).
% 1.26/0.56  fof(f3,axiom,(
% 1.26/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.26/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.26/0.56  fof(f43,plain,(
% 1.26/0.56    v1_funct_1(sK3)),
% 1.26/0.56    inference(cnf_transformation,[],[f18])).
% 1.26/0.56  fof(f18,plain,(
% 1.26/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.26/0.56    inference(flattening,[],[f17])).
% 1.26/0.56  fof(f17,plain,(
% 1.26/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.26/0.56    inference(ennf_transformation,[],[f16])).
% 1.26/0.56  fof(f16,negated_conjecture,(
% 1.26/0.56    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.26/0.56    inference(negated_conjecture,[],[f15])).
% 1.26/0.56  fof(f15,conjecture,(
% 1.26/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.26/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 1.26/0.56  fof(f129,plain,(
% 1.26/0.56    v1_relat_1(sK3)),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f45,f72])).
% 1.26/0.56  fof(f72,plain,(
% 1.26/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.26/0.56    inference(cnf_transformation,[],[f31])).
% 1.26/0.56  fof(f31,plain,(
% 1.26/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.56    inference(ennf_transformation,[],[f8])).
% 1.26/0.56  fof(f8,axiom,(
% 1.26/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.26/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.26/0.56  % (28901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.56  fof(f45,plain,(
% 1.26/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.26/0.56    inference(cnf_transformation,[],[f18])).
% 1.26/0.56  fof(f691,plain,(
% 1.26/0.56    k9_relat_1(sK3,k1_xboole_0) = k9_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0))),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f129,f43,f320,f357,f61])).
% 1.26/0.56  fof(f938,plain,(
% 1.26/0.56    sK1 = k9_relat_1(sK3,k1_xboole_0)),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f129,f43,f224,f908,f61])).
% 1.26/0.56  fof(f908,plain,(
% 1.26/0.56    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 1.26/0.56    inference(unit_resulting_resolution,[],[f901,f64])).
% 1.26/0.56  fof(f64,plain,(
% 1.26/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.26/0.56    inference(cnf_transformation,[],[f1])).
% 1.26/0.56  fof(f1,axiom,(
% 1.26/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.26/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.26/0.56  fof(f901,plain,(
% 1.26/0.56    v1_xboole_0(sK1)),
% 1.26/0.56    inference(global_subsumption,[],[f103,f865])).
% 1.26/0.56  fof(f865,plain,(
% 1.26/0.56    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK1)),
% 1.26/0.56    inference(superposition,[],[f46,f860])).
% 1.26/0.56  fof(f860,plain,(
% 1.26/0.56    k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 1.26/0.56    inference(resolution,[],[f852,f106])).
% 1.26/0.56  fof(f106,plain,(
% 1.26/0.56    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 1.26/0.56    inference(resolution,[],[f65,f37])).
% 1.26/0.56  fof(f37,plain,(
% 1.26/0.56    m1_subset_1(sK5,sK1)),
% 1.26/0.56    inference(cnf_transformation,[],[f18])).
% 1.26/0.56  fof(f65,plain,(
% 1.26/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.26/0.56    inference(cnf_transformation,[],[f24])).
% 1.26/0.56  fof(f24,plain,(
% 1.26/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.26/0.56    inference(flattening,[],[f23])).
% 1.26/0.56  fof(f23,plain,(
% 1.26/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.26/0.56    inference(ennf_transformation,[],[f4])).
% 1.26/0.57  fof(f4,axiom,(
% 1.26/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.26/0.57  fof(f852,plain,(
% 1.26/0.57    ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK2),
% 1.26/0.57    inference(superposition,[],[f847,f645])).
% 1.26/0.57  fof(f645,plain,(
% 1.26/0.57    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.26/0.57    inference(global_subsumption,[],[f44,f644])).
% 1.26/0.57  fof(f644,plain,(
% 1.26/0.57    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK1,sK2)),
% 1.26/0.57    inference(forward_demodulation,[],[f642,f302])).
% 1.26/0.57  fof(f302,plain,(
% 1.26/0.57    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f45,f74])).
% 1.26/0.57  fof(f74,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.57    inference(cnf_transformation,[],[f33])).
% 1.26/0.57  fof(f33,plain,(
% 1.26/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.57    inference(ennf_transformation,[],[f10])).
% 1.26/0.57  fof(f10,axiom,(
% 1.26/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.26/0.57  fof(f642,plain,(
% 1.26/0.57    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2)),
% 1.26/0.57    inference(resolution,[],[f82,f45])).
% 1.26/0.57  fof(f82,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f36])).
% 1.26/0.57  fof(f36,plain,(
% 1.26/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.57    inference(flattening,[],[f35])).
% 1.26/0.57  fof(f35,plain,(
% 1.26/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.57    inference(ennf_transformation,[],[f12])).
% 1.26/0.57  fof(f12,axiom,(
% 1.26/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.26/0.57  fof(f44,plain,(
% 1.26/0.57    v1_funct_2(sK3,sK1,sK2)),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  fof(f847,plain,(
% 1.26/0.57    ~r2_hidden(sK5,k1_relat_1(sK3))),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f841,f85])).
% 1.26/0.57  fof(f85,plain,(
% 1.26/0.57    ( ! [X0,X3] : (sP7(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.26/0.57    inference(equality_resolution,[],[f48])).
% 1.26/0.57  fof(f48,plain,(
% 1.26/0.57    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP7(X2,X0)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f20])).
% 1.26/0.57  fof(f20,plain,(
% 1.26/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.57    inference(flattening,[],[f19])).
% 1.26/0.57  fof(f19,plain,(
% 1.26/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.57    inference(ennf_transformation,[],[f6])).
% 1.26/0.57  fof(f6,axiom,(
% 1.26/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.26/0.57  fof(f841,plain,(
% 1.26/0.57    ~sP7(k1_funct_1(sK3,sK5),sK3)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f838,f657])).
% 1.26/0.57  fof(f657,plain,(
% 1.26/0.57    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK4)) | ~sP7(X0,sK3)) )),
% 1.26/0.57    inference(global_subsumption,[],[f43,f129,f653])).
% 1.26/0.57  fof(f653,plain,(
% 1.26/0.57    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~sP7(X0,sK3) | ~v1_relat_1(sK3)) )),
% 1.26/0.57    inference(resolution,[],[f307,f84])).
% 1.26/0.57  fof(f84,plain,(
% 1.26/0.57    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP7(X2,X0) | ~v1_relat_1(X0)) )),
% 1.26/0.57    inference(equality_resolution,[],[f51])).
% 1.26/0.57  fof(f51,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP7(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.26/0.57    inference(cnf_transformation,[],[f20])).
% 1.26/0.57  fof(f307,plain,(
% 1.26/0.57    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK3)) | r2_hidden(X2,k1_relat_1(sK4))) )),
% 1.26/0.57    inference(backward_demodulation,[],[f290,f301])).
% 1.26/0.57  fof(f301,plain,(
% 1.26/0.57    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f42,f74])).
% 1.26/0.57  fof(f42,plain,(
% 1.26/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  fof(f290,plain,(
% 1.26/0.57    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK3)) | r2_hidden(X2,k1_relset_1(sK2,sK0,sK4))) )),
% 1.26/0.57    inference(backward_demodulation,[],[f169,f284])).
% 1.26/0.57  fof(f284,plain,(
% 1.26/0.57    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f45,f73])).
% 1.26/0.57  fof(f73,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.57    inference(cnf_transformation,[],[f32])).
% 1.26/0.57  fof(f32,plain,(
% 1.26/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.57    inference(ennf_transformation,[],[f11])).
% 1.26/0.57  fof(f11,axiom,(
% 1.26/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.26/0.57  fof(f169,plain,(
% 1.26/0.57    ( ! [X2] : (~r2_hidden(X2,k2_relset_1(sK1,sK2,sK3)) | r2_hidden(X2,k1_relset_1(sK2,sK0,sK4))) )),
% 1.26/0.57    inference(resolution,[],[f67,f38])).
% 1.26/0.57  fof(f38,plain,(
% 1.26/0.57    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  fof(f67,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f27])).
% 1.26/0.57  fof(f27,plain,(
% 1.26/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.26/0.57    inference(ennf_transformation,[],[f2])).
% 1.26/0.57  fof(f2,axiom,(
% 1.26/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.26/0.57  fof(f838,plain,(
% 1.26/0.57    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f128,f41,f196,f823,f66])).
% 1.26/0.57  fof(f66,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f26])).
% 1.26/0.57  fof(f26,plain,(
% 1.26/0.57    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.26/0.57    inference(flattening,[],[f25])).
% 1.26/0.57  fof(f25,plain,(
% 1.26/0.57    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.26/0.57    inference(ennf_transformation,[],[f13])).
% 1.26/0.57  fof(f13,axiom,(
% 1.26/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.26/0.57  fof(f823,plain,(
% 1.26/0.57    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.26/0.57    inference(global_subsumption,[],[f46,f45,f44,f43,f42,f41,f39,f37,f309,f822])).
% 1.26/0.57  fof(f822,plain,(
% 1.26/0.57    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK5,sK1) | k1_xboole_0 = sK1 | v1_xboole_0(sK2)),
% 1.26/0.57    inference(forward_demodulation,[],[f821,f284])).
% 1.26/0.57  fof(f821,plain,(
% 1.26/0.57    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK5,sK1) | k1_xboole_0 = sK1 | v1_xboole_0(sK2)),
% 1.26/0.57    inference(forward_demodulation,[],[f816,f301])).
% 1.26/0.57  fof(f816,plain,(
% 1.26/0.57    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK2)),
% 1.26/0.57    inference(superposition,[],[f40,f71])).
% 1.26/0.57  fof(f71,plain,(
% 1.26/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | v1_xboole_0(X2)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f30])).
% 1.26/0.57  fof(f30,plain,(
% 1.26/0.57    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.26/0.57    inference(flattening,[],[f29])).
% 1.26/0.57  fof(f29,plain,(
% 1.26/0.57    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.26/0.57    inference(ennf_transformation,[],[f14])).
% 1.26/0.57  fof(f14,axiom,(
% 1.26/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.26/0.57  fof(f40,plain,(
% 1.26/0.57    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  fof(f309,plain,(
% 1.26/0.57    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 1.26/0.57    inference(backward_demodulation,[],[f288,f301])).
% 1.26/0.57  fof(f288,plain,(
% 1.26/0.57    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.26/0.57    inference(backward_demodulation,[],[f38,f284])).
% 1.26/0.57  fof(f196,plain,(
% 1.26/0.57    v5_relat_1(sK4,sK0)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f42,f76])).
% 1.26/0.57  fof(f76,plain,(
% 1.26/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f34])).
% 1.26/0.57  fof(f34,plain,(
% 1.26/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.57    inference(ennf_transformation,[],[f9])).
% 1.26/0.57  fof(f9,axiom,(
% 1.26/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.26/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.26/0.57  fof(f41,plain,(
% 1.26/0.57    v1_funct_1(sK4)),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  fof(f128,plain,(
% 1.26/0.57    v1_relat_1(sK4)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f42,f72])).
% 1.26/0.57  fof(f46,plain,(
% 1.26/0.57    ~v1_xboole_0(sK2)),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  fof(f103,plain,(
% 1.26/0.57    v1_xboole_0(k1_xboole_0)),
% 1.26/0.57    inference(unit_resulting_resolution,[],[f99,f63])).
% 1.26/0.57  fof(f63,plain,(
% 1.26/0.57    ( ! [X0] : (r2_hidden(sK12(X0),X0) | v1_xboole_0(X0)) )),
% 1.26/0.57    inference(cnf_transformation,[],[f1])).
% 1.26/0.57  fof(f39,plain,(
% 1.26/0.57    k1_xboole_0 != sK1),
% 1.26/0.57    inference(cnf_transformation,[],[f18])).
% 1.26/0.57  % SZS output end Proof for theBenchmark
% 1.26/0.57  % (28925)------------------------------
% 1.26/0.57  % (28925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.57  % (28925)Termination reason: Refutation
% 1.26/0.57  
% 1.26/0.57  % (28925)Memory used [KB]: 6780
% 1.26/0.57  % (28925)Time elapsed: 0.136 s
% 1.26/0.57  % (28925)------------------------------
% 1.26/0.57  % (28925)------------------------------
% 1.26/0.57  % (28900)Success in time 0.201 s
%------------------------------------------------------------------------------
