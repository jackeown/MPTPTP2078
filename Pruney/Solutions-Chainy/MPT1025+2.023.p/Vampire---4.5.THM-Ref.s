%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 674 expanded)
%              Number of leaves         :   11 ( 125 expanded)
%              Depth                    :   21
%              Number of atoms          :  282 (2735 expanded)
%              Number of equality atoms :   18 ( 393 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f382,f66])).

fof(f66,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

% (7655)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (7656)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (7648)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f382,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f381,f370])).

fof(f370,plain,(
    sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f368,f292])).

fof(f292,plain,(
    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f291,f158])).

fof(f158,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(resolution,[],[f76,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f73,f75])).

fof(f75,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f58,f36])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

% (7653)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f57,f36])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK4,X0) ) ),
    inference(backward_demodulation,[],[f69,f75])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK4,X0) ) ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f291,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f286,f105])).

fof(f105,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f83,f66])).

fof(f83,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f79,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f34,f75])).

fof(f286,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(resolution,[],[f154,f79])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2) ) ),
    inference(subsumption_resolution,[],[f153,f142])).

fof(f142,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f67,f135])).

fof(f135,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f87,f43])).

fof(f87,plain,(
    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f81,f66])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f79,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f44,f36])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f153,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f152,f36])).

fof(f152,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f147,f141])).

fof(f141,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f68,f135])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f45,f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f40,f75])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f368,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(resolution,[],[f303,f33])).

fof(f33,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f303,plain,(
    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f302,f158])).

fof(f302,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f297,f105])).

fof(f297,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(resolution,[],[f157,f79])).

fof(f157,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) ) ),
    inference(subsumption_resolution,[],[f156,f142])).

fof(f156,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f155,f36])).

fof(f155,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f141])).

fof(f148,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f38,f75])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f381,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f374,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f374,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f326,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f326,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f325,f158])).

fof(f325,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f320,f105])).

fof(f320,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(resolution,[],[f151,f79])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) ) ),
    inference(subsumption_resolution,[],[f150,f142])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f36])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f146,f141])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f39,f75])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (7650)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.45  % (7658)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.45  % (7663)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (7663)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f383,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f382,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f52,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  % (7655)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (7656)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (7648)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    ~v1_relat_1(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f381,f370])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 0.21/0.48    inference(subsumption_resolution,[],[f368,f292])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f291,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    m1_subset_1(sK4,sK1)),
% 0.21/0.48    inference(resolution,[],[f76,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f73,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.21/0.48    inference(resolution,[],[f58,f36])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  % (7653)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f57,f36])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f69,f75])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) )),
% 0.21/0.48    inference(resolution,[],[f56,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f286,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f89,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f66])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f79,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f34,f75])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.48    inference(resolution,[],[f154,f79])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~v1_xboole_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f87,f43])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f66])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f79,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | v1_xboole_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f44,f36])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f36])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f135])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | v1_xboole_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f45,f36])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(superposition,[],[f40,f75])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK5(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 0.21/0.48    inference(resolution,[],[f303,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f302,f158])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f297,f105])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.48    inference(resolution,[],[f157,f79])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f142])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f155,f36])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f141])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(superposition,[],[f38,f75])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f374,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f326,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f325,f158])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f320,f105])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.48    inference(resolution,[],[f151,f79])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f142])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f36])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f141])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(superposition,[],[f39,f75])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7663)------------------------------
% 0.21/0.48  % (7663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7663)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7663)Memory used [KB]: 2046
% 0.21/0.48  % (7663)Time elapsed: 0.061 s
% 0.21/0.48  % (7663)------------------------------
% 0.21/0.48  % (7663)------------------------------
% 0.21/0.48  % (7645)Success in time 0.125 s
%------------------------------------------------------------------------------
