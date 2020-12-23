%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:19 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 203 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  226 ( 868 expanded)
%              Number of equality atoms :   59 ( 163 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(subsumption_resolution,[],[f269,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f269,plain,(
    ~ r1_tarski(k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f126,f261])).

fof(f261,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f259,f183])).

fof(f183,plain,
    ( r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f176,f98])).

fof(f98,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f71,f76])).

fof(f76,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f71,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f70,f29])).

fof(f70,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f28,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f176,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    inference(resolution,[],[f166,f29])).

fof(f166,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f163,f79])).

fof(f79,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f26,f72])).

fof(f72,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0) ),
    inference(resolution,[],[f29,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f26,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f163,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X5))
      | r2_hidden(sK6(sK3,X5,X4),k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f131,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | r2_hidden(sK6(sK3,X0,X1),k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f69,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f69,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(sK6(sK3,X15,X16),k1_relat_1(sK3))
      | ~ r2_hidden(X16,k9_relat_1(sK3,X15)) ) ),
    inference(resolution,[],[f27,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f259,plain,(
    ~ r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    inference(backward_demodulation,[],[f155,f249])).

fof(f249,plain,(
    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(resolution,[],[f239,f29])).

fof(f239,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ) ),
    inference(resolution,[],[f203,f79])).

fof(f203,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X5))
      | k1_funct_1(sK3,sK6(sK3,X5,X4)) = X4
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f132,f40])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f67,f31])).

fof(f67,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(sK3)
      | k1_funct_1(sK3,sK6(sK3,X11,X12)) = X12
      | ~ r2_hidden(X12,k9_relat_1(sK3,X11)) ) ),
    inference(resolution,[],[f27,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f155,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(resolution,[],[f154,f25])).

fof(f25,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f154,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK2) ),
    inference(resolution,[],[f144,f29])).

fof(f144,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | r2_hidden(sK6(sK3,sK2,sK4),sK2) ) ),
    inference(resolution,[],[f141,f79])).

fof(f141,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X5))
      | r2_hidden(sK6(sK3,X5,X4),X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f130,f40])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | r2_hidden(sK6(sK3,X0,X1),X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f68,f31])).

fof(f68,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(sK6(sK3,X13,X14),X13)
      | ~ r2_hidden(X14,k9_relat_1(sK3,X13)) ) ),
    inference(resolution,[],[f27,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f126,plain,(
    ~ r1_tarski(sK1,sK4) ),
    inference(resolution,[],[f121,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f121,plain,(
    r2_hidden(sK4,sK1) ),
    inference(resolution,[],[f84,f108])).

fof(f108,plain,(
    ! [X1] : m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f107,f29])).

fof(f107,plain,(
    ! [X1] :
      ( m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f50,f72])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
      | r2_hidden(sK4,X0) ) ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (806060032)
% 0.13/0.37  ipcrm: permission denied for id (808747009)
% 0.13/0.37  ipcrm: permission denied for id (806092802)
% 0.13/0.38  ipcrm: permission denied for id (806223878)
% 0.13/0.38  ipcrm: permission denied for id (806256647)
% 0.13/0.38  ipcrm: permission denied for id (806289416)
% 0.13/0.38  ipcrm: permission denied for id (806322185)
% 0.13/0.38  ipcrm: permission denied for id (808878090)
% 0.13/0.38  ipcrm: permission denied for id (806387723)
% 0.13/0.39  ipcrm: permission denied for id (806420492)
% 0.13/0.39  ipcrm: permission denied for id (806486031)
% 0.13/0.39  ipcrm: permission denied for id (809009168)
% 0.13/0.39  ipcrm: permission denied for id (806551569)
% 0.13/0.40  ipcrm: permission denied for id (809140245)
% 0.13/0.40  ipcrm: permission denied for id (809205783)
% 0.13/0.40  ipcrm: permission denied for id (806715416)
% 0.13/0.40  ipcrm: permission denied for id (809238553)
% 0.13/0.40  ipcrm: permission denied for id (806748187)
% 0.13/0.41  ipcrm: permission denied for id (809304092)
% 0.13/0.41  ipcrm: permission denied for id (809369630)
% 0.13/0.41  ipcrm: permission denied for id (809402399)
% 0.13/0.41  ipcrm: permission denied for id (806813728)
% 0.13/0.41  ipcrm: permission denied for id (809435169)
% 0.13/0.41  ipcrm: permission denied for id (806846498)
% 0.13/0.42  ipcrm: permission denied for id (806912036)
% 0.13/0.42  ipcrm: permission denied for id (806977575)
% 0.13/0.42  ipcrm: permission denied for id (809566248)
% 0.13/0.42  ipcrm: permission denied for id (809631786)
% 0.13/0.43  ipcrm: permission denied for id (809697324)
% 0.13/0.43  ipcrm: permission denied for id (809730093)
% 0.22/0.43  ipcrm: permission denied for id (807075887)
% 0.22/0.43  ipcrm: permission denied for id (809828401)
% 0.22/0.43  ipcrm: permission denied for id (809861170)
% 0.22/0.43  ipcrm: permission denied for id (809893939)
% 0.22/0.44  ipcrm: permission denied for id (807174198)
% 0.22/0.44  ipcrm: permission denied for id (809992247)
% 0.22/0.44  ipcrm: permission denied for id (807239739)
% 0.22/0.44  ipcrm: permission denied for id (810156092)
% 0.22/0.45  ipcrm: permission denied for id (807305278)
% 0.22/0.45  ipcrm: permission denied for id (810221631)
% 0.22/0.45  ipcrm: permission denied for id (807338048)
% 0.22/0.45  ipcrm: permission denied for id (810319939)
% 0.22/0.45  ipcrm: permission denied for id (807403588)
% 0.22/0.46  ipcrm: permission denied for id (807436357)
% 0.22/0.46  ipcrm: permission denied for id (807469126)
% 0.22/0.46  ipcrm: permission denied for id (810385480)
% 0.22/0.46  ipcrm: permission denied for id (807600202)
% 0.22/0.46  ipcrm: permission denied for id (807632971)
% 0.22/0.47  ipcrm: permission denied for id (810582096)
% 0.22/0.47  ipcrm: permission denied for id (810614865)
% 0.22/0.47  ipcrm: permission denied for id (810647634)
% 0.22/0.48  ipcrm: permission denied for id (810745941)
% 0.22/0.48  ipcrm: permission denied for id (810778710)
% 0.22/0.48  ipcrm: permission denied for id (810811479)
% 0.22/0.48  ipcrm: permission denied for id (810844248)
% 0.22/0.48  ipcrm: permission denied for id (810877017)
% 0.22/0.48  ipcrm: permission denied for id (810942555)
% 0.22/0.48  ipcrm: permission denied for id (810975324)
% 0.22/0.49  ipcrm: permission denied for id (807862365)
% 0.22/0.49  ipcrm: permission denied for id (807927902)
% 0.22/0.49  ipcrm: permission denied for id (811040864)
% 0.22/0.49  ipcrm: permission denied for id (811073633)
% 0.22/0.49  ipcrm: permission denied for id (811139171)
% 0.22/0.50  ipcrm: permission denied for id (811303016)
% 0.22/0.50  ipcrm: permission denied for id (811335785)
% 0.22/0.50  ipcrm: permission denied for id (811368554)
% 0.22/0.50  ipcrm: permission denied for id (808190059)
% 0.22/0.50  ipcrm: permission denied for id (808222828)
% 0.22/0.51  ipcrm: permission denied for id (811401325)
% 0.22/0.51  ipcrm: permission denied for id (808321134)
% 0.22/0.51  ipcrm: permission denied for id (808353903)
% 0.22/0.51  ipcrm: permission denied for id (808386672)
% 0.22/0.51  ipcrm: permission denied for id (808419441)
% 0.22/0.51  ipcrm: permission denied for id (808452210)
% 0.22/0.51  ipcrm: permission denied for id (808484979)
% 0.22/0.51  ipcrm: permission denied for id (808517748)
% 0.22/0.52  ipcrm: permission denied for id (808550517)
% 0.22/0.52  ipcrm: permission denied for id (811466871)
% 0.22/0.52  ipcrm: permission denied for id (811499640)
% 0.22/0.52  ipcrm: permission denied for id (811532409)
% 0.22/0.52  ipcrm: permission denied for id (808583291)
% 0.22/0.52  ipcrm: permission denied for id (811597948)
% 0.22/0.53  ipcrm: permission denied for id (808648829)
% 0.22/0.53  ipcrm: permission denied for id (808681598)
% 0.22/0.53  ipcrm: permission denied for id (808714367)
% 0.67/0.63  % (24394)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.67/0.63  % (24395)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.67/0.64  % (24406)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.67/0.64  % (24394)Refutation not found, incomplete strategy% (24394)------------------------------
% 0.67/0.64  % (24394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.67/0.64  % (24394)Termination reason: Refutation not found, incomplete strategy
% 0.67/0.64  
% 0.67/0.64  % (24394)Memory used [KB]: 10618
% 0.67/0.64  % (24394)Time elapsed: 0.070 s
% 0.67/0.64  % (24394)------------------------------
% 0.67/0.64  % (24394)------------------------------
% 1.07/0.64  % (24399)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.07/0.64  % (24401)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.07/0.64  % (24393)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.07/0.65  % (24408)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.07/0.65  % (24400)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.07/0.65  % (24406)Refutation found. Thanks to Tanya!
% 1.07/0.65  % SZS status Theorem for theBenchmark
% 1.07/0.65  % SZS output start Proof for theBenchmark
% 1.07/0.65  fof(f276,plain,(
% 1.07/0.65    $false),
% 1.07/0.65    inference(subsumption_resolution,[],[f269,f30])).
% 1.07/0.65  fof(f30,plain,(
% 1.07/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.07/0.65    inference(cnf_transformation,[],[f1])).
% 1.07/0.65  fof(f1,axiom,(
% 1.07/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.07/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.07/0.65  fof(f269,plain,(
% 1.07/0.65    ~r1_tarski(k1_xboole_0,sK4)),
% 1.07/0.65    inference(backward_demodulation,[],[f126,f261])).
% 1.07/0.65  fof(f261,plain,(
% 1.07/0.65    k1_xboole_0 = sK1),
% 1.07/0.65    inference(resolution,[],[f259,f183])).
% 1.07/0.65  fof(f183,plain,(
% 1.07/0.65    r2_hidden(sK6(sK3,sK2,sK4),sK0) | k1_xboole_0 = sK1),
% 1.07/0.65    inference(superposition,[],[f176,f98])).
% 1.07/0.65  fof(f98,plain,(
% 1.07/0.65    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.07/0.65    inference(superposition,[],[f71,f76])).
% 1.07/0.65  fof(f76,plain,(
% 1.07/0.65    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.07/0.65    inference(resolution,[],[f29,f43])).
% 1.07/0.65  fof(f43,plain,(
% 1.07/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.07/0.65    inference(cnf_transformation,[],[f20])).
% 1.07/0.65  fof(f20,plain,(
% 1.07/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/0.65    inference(ennf_transformation,[],[f8])).
% 1.07/0.65  fof(f8,axiom,(
% 1.07/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.07/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.07/0.65  fof(f29,plain,(
% 1.07/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.07/0.65    inference(cnf_transformation,[],[f14])).
% 1.07/0.65  fof(f14,plain,(
% 1.07/0.65    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.07/0.65    inference(flattening,[],[f13])).
% 1.07/0.65  fof(f13,plain,(
% 1.07/0.65    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.07/0.65    inference(ennf_transformation,[],[f12])).
% 1.07/0.65  fof(f12,negated_conjecture,(
% 1.07/0.65    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.07/0.65    inference(negated_conjecture,[],[f11])).
% 1.07/0.65  fof(f11,conjecture,(
% 1.07/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.07/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 1.07/0.65  fof(f71,plain,(
% 1.07/0.65    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.07/0.65    inference(subsumption_resolution,[],[f70,f29])).
% 1.07/0.65  fof(f70,plain,(
% 1.07/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.07/0.65    inference(resolution,[],[f28,f49])).
% 1.07/0.65  fof(f49,plain,(
% 1.07/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.07/0.65    inference(cnf_transformation,[],[f22])).
% 1.07/0.65  fof(f22,plain,(
% 1.07/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/0.65    inference(flattening,[],[f21])).
% 1.07/0.65  fof(f21,plain,(
% 1.07/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/0.65    inference(ennf_transformation,[],[f10])).
% 1.07/0.65  fof(f10,axiom,(
% 1.07/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.07/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.07/0.65  fof(f28,plain,(
% 1.07/0.65    v1_funct_2(sK3,sK0,sK1)),
% 1.07/0.65    inference(cnf_transformation,[],[f14])).
% 1.07/0.65  fof(f176,plain,(
% 1.07/0.65    r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))),
% 1.07/0.65    inference(resolution,[],[f166,f29])).
% 1.07/0.65  fof(f166,plain,(
% 1.07/0.65    ( ! [X10,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))) )),
% 1.07/0.65    inference(resolution,[],[f163,f79])).
% 1.07/0.65  fof(f79,plain,(
% 1.07/0.65    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.07/0.65    inference(backward_demodulation,[],[f26,f72])).
% 1.07/0.65  fof(f72,plain,(
% 1.07/0.65    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) )),
% 1.07/0.65    inference(resolution,[],[f29,f51])).
% 1.07/0.65  fof(f51,plain,(
% 1.07/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.07/0.65    inference(cnf_transformation,[],[f24])).
% 1.07/0.65  fof(f24,plain,(
% 1.07/0.65    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/0.65    inference(ennf_transformation,[],[f9])).
% 1.07/0.65  fof(f9,axiom,(
% 1.07/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.07/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.16/0.65  fof(f26,plain,(
% 1.16/0.65    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.16/0.65    inference(cnf_transformation,[],[f14])).
% 1.16/0.65  fof(f163,plain,(
% 1.16/0.65    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k9_relat_1(sK3,X5)) | r2_hidden(sK6(sK3,X5,X4),k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 1.16/0.65    inference(resolution,[],[f131,f40])).
% 1.16/0.65  fof(f40,plain,(
% 1.16/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.16/0.65    inference(cnf_transformation,[],[f4])).
% 1.16/0.65  fof(f4,axiom,(
% 1.16/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.16/0.65  fof(f131,plain,(
% 1.16/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | r2_hidden(sK6(sK3,X0,X1),k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) )),
% 1.16/0.65    inference(resolution,[],[f69,f31])).
% 1.16/0.65  fof(f31,plain,(
% 1.16/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.16/0.65    inference(cnf_transformation,[],[f15])).
% 1.16/0.65  fof(f15,plain,(
% 1.16/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.16/0.65    inference(ennf_transformation,[],[f3])).
% 1.16/0.65  fof(f3,axiom,(
% 1.16/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.16/0.65  fof(f69,plain,(
% 1.16/0.65    ( ! [X15,X16] : (~v1_relat_1(sK3) | r2_hidden(sK6(sK3,X15,X16),k1_relat_1(sK3)) | ~r2_hidden(X16,k9_relat_1(sK3,X15))) )),
% 1.16/0.65    inference(resolution,[],[f27,f56])).
% 1.16/0.65  fof(f56,plain,(
% 1.16/0.65    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.16/0.65    inference(equality_resolution,[],[f36])).
% 1.16/0.65  fof(f36,plain,(
% 1.16/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.16/0.65    inference(cnf_transformation,[],[f17])).
% 1.16/0.65  fof(f17,plain,(
% 1.16/0.65    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.16/0.65    inference(flattening,[],[f16])).
% 1.16/0.65  fof(f16,plain,(
% 1.16/0.65    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.16/0.65    inference(ennf_transformation,[],[f5])).
% 1.16/0.65  fof(f5,axiom,(
% 1.16/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 1.16/0.65  fof(f27,plain,(
% 1.16/0.65    v1_funct_1(sK3)),
% 1.16/0.65    inference(cnf_transformation,[],[f14])).
% 1.16/0.65  fof(f259,plain,(
% 1.16/0.65    ~r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 1.16/0.65    inference(trivial_inequality_removal,[],[f250])).
% 1.16/0.65  fof(f250,plain,(
% 1.16/0.65    sK4 != sK4 | ~r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 1.16/0.65    inference(backward_demodulation,[],[f155,f249])).
% 1.16/0.65  fof(f249,plain,(
% 1.16/0.65    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 1.16/0.65    inference(resolution,[],[f239,f29])).
% 1.16/0.65  fof(f239,plain,(
% 1.16/0.65    ( ! [X10,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))) )),
% 1.16/0.65    inference(resolution,[],[f203,f79])).
% 1.16/0.65  fof(f203,plain,(
% 1.16/0.65    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k9_relat_1(sK3,X5)) | k1_funct_1(sK3,sK6(sK3,X5,X4)) = X4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 1.16/0.65    inference(resolution,[],[f132,f40])).
% 1.16/0.65  fof(f132,plain,(
% 1.16/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) )),
% 1.16/0.65    inference(resolution,[],[f67,f31])).
% 1.16/0.65  fof(f67,plain,(
% 1.16/0.65    ( ! [X12,X11] : (~v1_relat_1(sK3) | k1_funct_1(sK3,sK6(sK3,X11,X12)) = X12 | ~r2_hidden(X12,k9_relat_1(sK3,X11))) )),
% 1.16/0.65    inference(resolution,[],[f27,f54])).
% 1.16/0.65  fof(f54,plain,(
% 1.16/0.65    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.16/0.65    inference(equality_resolution,[],[f38])).
% 1.16/0.65  fof(f38,plain,(
% 1.16/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.16/0.65    inference(cnf_transformation,[],[f17])).
% 1.16/0.65  fof(f155,plain,(
% 1.16/0.65    ~r2_hidden(sK6(sK3,sK2,sK4),sK0) | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 1.16/0.65    inference(resolution,[],[f154,f25])).
% 1.16/0.65  fof(f25,plain,(
% 1.16/0.65    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.16/0.65    inference(cnf_transformation,[],[f14])).
% 1.16/0.65  fof(f154,plain,(
% 1.16/0.65    r2_hidden(sK6(sK3,sK2,sK4),sK2)),
% 1.16/0.65    inference(resolution,[],[f144,f29])).
% 1.16/0.65  fof(f144,plain,(
% 1.16/0.65    ( ! [X10,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | r2_hidden(sK6(sK3,sK2,sK4),sK2)) )),
% 1.16/0.65    inference(resolution,[],[f141,f79])).
% 1.16/0.65  fof(f141,plain,(
% 1.16/0.65    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k9_relat_1(sK3,X5)) | r2_hidden(sK6(sK3,X5,X4),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 1.16/0.65    inference(resolution,[],[f130,f40])).
% 1.16/0.65  fof(f130,plain,(
% 1.16/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | r2_hidden(sK6(sK3,X0,X1),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) )),
% 1.16/0.65    inference(resolution,[],[f68,f31])).
% 1.16/0.65  fof(f68,plain,(
% 1.16/0.65    ( ! [X14,X13] : (~v1_relat_1(sK3) | r2_hidden(sK6(sK3,X13,X14),X13) | ~r2_hidden(X14,k9_relat_1(sK3,X13))) )),
% 1.16/0.65    inference(resolution,[],[f27,f55])).
% 1.16/0.65  fof(f55,plain,(
% 1.16/0.65    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.16/0.65    inference(equality_resolution,[],[f37])).
% 1.16/0.65  fof(f37,plain,(
% 1.16/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.16/0.65    inference(cnf_transformation,[],[f17])).
% 1.16/0.65  fof(f126,plain,(
% 1.16/0.65    ~r1_tarski(sK1,sK4)),
% 1.16/0.65    inference(resolution,[],[f121,f42])).
% 1.16/0.65  fof(f42,plain,(
% 1.16/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.16/0.65    inference(cnf_transformation,[],[f19])).
% 1.16/0.65  fof(f19,plain,(
% 1.16/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.16/0.65    inference(ennf_transformation,[],[f6])).
% 1.16/0.65  fof(f6,axiom,(
% 1.16/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.16/0.65  fof(f121,plain,(
% 1.16/0.65    r2_hidden(sK4,sK1)),
% 1.16/0.65    inference(resolution,[],[f84,f108])).
% 1.16/0.65  fof(f108,plain,(
% 1.16/0.65    ( ! [X1] : (m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(sK1))) )),
% 1.16/0.65    inference(subsumption_resolution,[],[f107,f29])).
% 1.16/0.65  fof(f107,plain,(
% 1.16/0.65    ( ! [X1] : (m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.16/0.65    inference(superposition,[],[f50,f72])).
% 1.16/0.65  fof(f50,plain,(
% 1.16/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 1.16/0.65    inference(cnf_transformation,[],[f23])).
% 1.16/0.65  fof(f23,plain,(
% 1.16/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.16/0.65    inference(ennf_transformation,[],[f7])).
% 1.16/0.65  fof(f7,axiom,(
% 1.16/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.16/0.65  fof(f84,plain,(
% 1.16/0.65    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | r2_hidden(sK4,X0)) )),
% 1.16/0.65    inference(resolution,[],[f79,f41])).
% 1.16/0.65  fof(f41,plain,(
% 1.16/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.16/0.65    inference(cnf_transformation,[],[f18])).
% 1.16/0.65  fof(f18,plain,(
% 1.16/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.65    inference(ennf_transformation,[],[f2])).
% 1.16/0.65  fof(f2,axiom,(
% 1.16/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.16/0.65  % SZS output end Proof for theBenchmark
% 1.16/0.65  % (24406)------------------------------
% 1.16/0.65  % (24406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.65  % (24406)Termination reason: Refutation
% 1.16/0.65  
% 1.16/0.65  % (24406)Memory used [KB]: 1791
% 1.16/0.65  % (24406)Time elapsed: 0.015 s
% 1.16/0.65  % (24406)------------------------------
% 1.16/0.65  % (24406)------------------------------
% 1.16/0.65  % (24238)Success in time 0.286 s
%------------------------------------------------------------------------------
