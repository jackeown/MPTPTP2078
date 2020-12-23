%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:53 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 865 expanded)
%              Number of leaves         :   13 ( 175 expanded)
%              Depth                    :   23
%              Number of atoms          :  250 (3662 expanded)
%              Number of equality atoms :   72 ( 947 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(global_subsumption,[],[f396,f441])).

fof(f441,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f74,f31,f437,f100])).

fof(f100,plain,(
    ! [X0] :
      ( sP5(sK7(k2_relat_1(X0),k1_xboole_0),X0)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f95,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f45,f72])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

% (13539)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f437,plain,(
    ! [X0] : ~ sP5(X0,sK2) ),
    inference(global_subsumption,[],[f72,f409])).

fof(f409,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP5(X0,sK2) ) ),
    inference(backward_demodulation,[],[f250,f384])).

fof(f384,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f327,f378])).

fof(f378,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f342,f376])).

fof(f376,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f32,f375])).

fof(f375,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f374,f133])).

fof(f133,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f33,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f374,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f60,f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f342,plain,(
    ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f325,f338,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f66,f30])).

fof(f30,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f338,plain,(
    ~ sP5(sK4(sK2,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f74,f31,f142,f325,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f142,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f33,f141])).

fof(f141,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f34,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f34,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f325,plain,(
    r2_hidden(sK4(sK2,sK1),sK1) ),
    inference(global_subsumption,[],[f142,f324])).

fof(f324,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(factoring,[],[f323])).

fof(f323,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK4(sK2,X0),X0) ) ),
    inference(global_subsumption,[],[f31,f74,f320])).

fof(f320,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),X0)
      | k2_relat_1(sK2) = X0
      | r2_hidden(sK4(sK2,X0),sK1) ) ),
    inference(resolution,[],[f42,f250])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f327,plain,(
    r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f325,f29])).

fof(f29,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f250,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f31,f74,f244])).

fof(f244,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ v1_funct_1(sK2)
      | ~ sP5(X0,sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f237,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f230,f76])).

fof(f76,plain,(
    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f74,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f230,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,k9_relat_1(sK2,X15))
      | r2_hidden(X14,sK1) ) ),
    inference(global_subsumption,[],[f74,f222])).

fof(f222,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X14,k9_relat_1(sK2,X15))
      | r2_hidden(X14,sK1) ) ),
    inference(resolution,[],[f49,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f396,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f142,f384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (13538)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (13530)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (13532)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (13548)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (13540)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (13546)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.60  % (13524)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.60  % (13529)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.60  % (13528)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.61  % (13548)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.61  % (13526)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.61  % (13545)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.61  % (13547)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.61  % (13537)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.59/0.61  % SZS output start Proof for theBenchmark
% 1.59/0.61  fof(f445,plain,(
% 1.59/0.61    $false),
% 1.59/0.61    inference(global_subsumption,[],[f396,f441])).
% 1.59/0.61  fof(f441,plain,(
% 1.59/0.61    k1_xboole_0 = k2_relat_1(sK2)),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f74,f31,f437,f100])).
% 1.59/0.61  fof(f100,plain,(
% 1.59/0.61    ( ! [X0] : (sP5(sK7(k2_relat_1(X0),k1_xboole_0),X0) | ~v1_funct_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(resolution,[],[f95,f64])).
% 1.59/0.61  fof(f64,plain,(
% 1.59/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(equality_resolution,[],[f41])).
% 1.59/0.61  fof(f41,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.59/0.61    inference(cnf_transformation,[],[f19])).
% 1.59/0.61  fof(f19,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(flattening,[],[f18])).
% 1.93/0.61  fof(f18,plain,(
% 1.93/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.93/0.61    inference(ennf_transformation,[],[f7])).
% 1.93/0.62  fof(f7,axiom,(
% 1.93/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.93/0.62  fof(f95,plain,(
% 1.93/0.62    ( ! [X0] : (r2_hidden(sK7(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.93/0.62    inference(resolution,[],[f45,f72])).
% 1.93/0.62  fof(f72,plain,(
% 1.93/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f35,f47])).
% 1.93/0.62  fof(f47,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f22])).
% 1.93/0.62  fof(f22,plain,(
% 1.93/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.93/0.62    inference(ennf_transformation,[],[f8])).
% 1.93/0.62  % (13539)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.93/0.62  fof(f8,axiom,(
% 1.93/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.93/0.62  fof(f35,plain,(
% 1.93/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f2])).
% 1.93/0.62  fof(f2,axiom,(
% 1.93/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.93/0.62  fof(f45,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0) | X0 = X1) )),
% 1.93/0.62    inference(cnf_transformation,[],[f21])).
% 1.93/0.62  fof(f21,plain,(
% 1.93/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.93/0.62    inference(ennf_transformation,[],[f1])).
% 1.93/0.62  fof(f1,axiom,(
% 1.93/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.93/0.62  fof(f437,plain,(
% 1.93/0.62    ( ! [X0] : (~sP5(X0,sK2)) )),
% 1.93/0.62    inference(global_subsumption,[],[f72,f409])).
% 1.93/0.62  fof(f409,plain,(
% 1.93/0.62    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP5(X0,sK2)) )),
% 1.93/0.62    inference(backward_demodulation,[],[f250,f384])).
% 1.93/0.62  fof(f384,plain,(
% 1.93/0.62    k1_xboole_0 = sK1),
% 1.93/0.62    inference(global_subsumption,[],[f327,f378])).
% 1.93/0.62  fof(f378,plain,(
% 1.93/0.62    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | k1_xboole_0 = sK1),
% 1.93/0.62    inference(superposition,[],[f342,f376])).
% 1.93/0.62  fof(f376,plain,(
% 1.93/0.62    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.93/0.62    inference(global_subsumption,[],[f32,f375])).
% 1.93/0.62  fof(f375,plain,(
% 1.93/0.62    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 1.93/0.62    inference(forward_demodulation,[],[f374,f133])).
% 1.93/0.62  fof(f133,plain,(
% 1.93/0.62    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f33,f53])).
% 1.93/0.62  fof(f53,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.62    inference(cnf_transformation,[],[f25])).
% 1.93/0.62  fof(f25,plain,(
% 1.93/0.62    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(ennf_transformation,[],[f10])).
% 1.93/0.62  fof(f10,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.93/0.62  fof(f33,plain,(
% 1.93/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f16,plain,(
% 1.93/0.62    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.93/0.62    inference(flattening,[],[f15])).
% 1.93/0.62  fof(f15,plain,(
% 1.93/0.62    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.93/0.62    inference(ennf_transformation,[],[f14])).
% 1.93/0.62  fof(f14,negated_conjecture,(
% 1.93/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.93/0.62    inference(negated_conjecture,[],[f13])).
% 1.93/0.62  fof(f13,conjecture,(
% 1.93/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.93/0.62  fof(f374,plain,(
% 1.93/0.62    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.93/0.62    inference(resolution,[],[f60,f33])).
% 1.93/0.62  fof(f60,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f28])).
% 1.93/0.62  fof(f28,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(flattening,[],[f27])).
% 1.93/0.62  fof(f27,plain,(
% 1.93/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(ennf_transformation,[],[f12])).
% 1.93/0.62  fof(f12,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.93/0.62  fof(f32,plain,(
% 1.93/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f342,plain,(
% 1.93/0.62    ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f325,f338,f77])).
% 1.93/0.62  fof(f77,plain,(
% 1.93/0.62    ( ! [X0] : (~r2_hidden(sK3(X0),k1_relat_1(sK2)) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 1.93/0.62    inference(superposition,[],[f66,f30])).
% 1.93/0.62  fof(f30,plain,(
% 1.93/0.62    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f66,plain,(
% 1.93/0.62    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.93/0.62    inference(equality_resolution,[],[f37])).
% 1.93/0.62  fof(f37,plain,(
% 1.93/0.62    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f19])).
% 1.93/0.62  fof(f338,plain,(
% 1.93/0.62    ~sP5(sK4(sK2,sK1),sK2)),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f74,f31,f142,f325,f43])).
% 1.93/0.62  fof(f43,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.93/0.62    inference(cnf_transformation,[],[f19])).
% 1.93/0.62  fof(f142,plain,(
% 1.93/0.62    sK1 != k2_relat_1(sK2)),
% 1.93/0.62    inference(global_subsumption,[],[f33,f141])).
% 1.93/0.62  fof(f141,plain,(
% 1.93/0.62    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.62    inference(superposition,[],[f34,f54])).
% 1.93/0.62  fof(f54,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.62    inference(cnf_transformation,[],[f26])).
% 1.93/0.62  fof(f26,plain,(
% 1.93/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(ennf_transformation,[],[f11])).
% 1.93/0.62  fof(f11,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.93/0.62  fof(f34,plain,(
% 1.93/0.62    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f325,plain,(
% 1.93/0.62    r2_hidden(sK4(sK2,sK1),sK1)),
% 1.93/0.62    inference(global_subsumption,[],[f142,f324])).
% 1.93/0.62  fof(f324,plain,(
% 1.93/0.62    r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2)),
% 1.93/0.62    inference(factoring,[],[f323])).
% 1.93/0.62  fof(f323,plain,(
% 1.93/0.62    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0)) )),
% 1.93/0.62    inference(global_subsumption,[],[f31,f74,f320])).
% 1.93/0.62  fof(f320,plain,(
% 1.93/0.62    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),sK1)) )),
% 1.93/0.62    inference(resolution,[],[f42,f250])).
% 1.93/0.62  fof(f42,plain,(
% 1.93/0.62    ( ! [X0,X1] : (sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.93/0.62    inference(cnf_transformation,[],[f19])).
% 1.93/0.62  fof(f327,plain,(
% 1.93/0.62    r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f325,f29])).
% 1.93/0.62  fof(f29,plain,(
% 1.93/0.62    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f250,plain,(
% 1.93/0.62    ( ! [X0] : (~sP5(X0,sK2) | r2_hidden(X0,sK1)) )),
% 1.93/0.62    inference(global_subsumption,[],[f31,f74,f244])).
% 1.93/0.62  fof(f244,plain,(
% 1.93/0.62    ( ! [X0] : (r2_hidden(X0,sK1) | ~v1_funct_1(sK2) | ~sP5(X0,sK2) | ~v1_relat_1(sK2)) )),
% 1.93/0.62    inference(resolution,[],[f237,f65])).
% 1.93/0.62  fof(f65,plain,(
% 1.93/0.62    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 1.93/0.62    inference(equality_resolution,[],[f40])).
% 1.93/0.62  fof(f40,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.93/0.62    inference(cnf_transformation,[],[f19])).
% 1.93/0.62  fof(f237,plain,(
% 1.93/0.62    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 1.93/0.62    inference(superposition,[],[f230,f76])).
% 1.93/0.62  fof(f76,plain,(
% 1.93/0.62    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f74,f36])).
% 1.93/0.62  fof(f36,plain,(
% 1.93/0.62    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f17])).
% 1.93/0.62  fof(f17,plain,(
% 1.93/0.62    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.93/0.62    inference(ennf_transformation,[],[f6])).
% 1.93/0.62  fof(f6,axiom,(
% 1.93/0.62    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.93/0.62  fof(f230,plain,(
% 1.93/0.62    ( ! [X14,X15] : (~r2_hidden(X14,k9_relat_1(sK2,X15)) | r2_hidden(X14,sK1)) )),
% 1.93/0.62    inference(global_subsumption,[],[f74,f222])).
% 1.93/0.62  fof(f222,plain,(
% 1.93/0.62    ( ! [X14,X15] : (~v1_relat_1(sK2) | ~r2_hidden(X14,k9_relat_1(sK2,X15)) | r2_hidden(X14,sK1)) )),
% 1.93/0.62    inference(resolution,[],[f49,f83])).
% 1.93/0.62  fof(f83,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(X0,sK1)) )),
% 1.93/0.62    inference(resolution,[],[f62,f79])).
% 1.93/0.62  fof(f79,plain,(
% 1.93/0.62    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.93/0.62    inference(resolution,[],[f44,f33])).
% 1.93/0.62  fof(f44,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f20])).
% 1.93/0.62  fof(f20,plain,(
% 1.93/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.62    inference(ennf_transformation,[],[f4])).
% 1.93/0.62  fof(f4,axiom,(
% 1.93/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.93/0.62  fof(f62,plain,(
% 1.93/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f3])).
% 1.93/0.62  fof(f3,axiom,(
% 1.93/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.93/0.62  fof(f49,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.93/0.62    inference(cnf_transformation,[],[f23])).
% 1.93/0.62  fof(f23,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.93/0.62    inference(ennf_transformation,[],[f5])).
% 1.93/0.62  fof(f5,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.93/0.62  fof(f31,plain,(
% 1.93/0.62    v1_funct_1(sK2)),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f74,plain,(
% 1.93/0.62    v1_relat_1(sK2)),
% 1.93/0.62    inference(unit_resulting_resolution,[],[f33,f52])).
% 1.93/0.62  fof(f52,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f24])).
% 1.93/0.62  fof(f24,plain,(
% 1.93/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(ennf_transformation,[],[f9])).
% 1.93/0.62  fof(f9,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.93/0.62  fof(f396,plain,(
% 1.93/0.62    k1_xboole_0 != k2_relat_1(sK2)),
% 1.93/0.62    inference(backward_demodulation,[],[f142,f384])).
% 1.93/0.62  % SZS output end Proof for theBenchmark
% 1.93/0.62  % (13548)------------------------------
% 1.93/0.62  % (13548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.62  % (13548)Termination reason: Refutation
% 1.93/0.62  
% 1.93/0.62  % (13548)Memory used [KB]: 6780
% 1.93/0.62  % (13548)Time elapsed: 0.146 s
% 1.93/0.62  % (13548)------------------------------
% 1.93/0.62  % (13548)------------------------------
% 1.93/0.62  % (13553)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.93/0.62  % (13531)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.93/0.63  % (13523)Success in time 0.258 s
%------------------------------------------------------------------------------
