%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 166 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 ( 722 expanded)
%              Number of equality atoms :   31 ( 111 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12612)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f235,f209])).

fof(f209,plain,(
    sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(resolution,[],[f198,f136])).

fof(f136,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(resolution,[],[f125,f19])).

fof(f19,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f125,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK2) ),
    inference(resolution,[],[f119,f62])).

fof(f62,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f20,f59])).

fof(f59,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0) ),
    inference(resolution,[],[f23,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | r2_hidden(sK6(sK3,X0,X1),X0) ) ),
    inference(resolution,[],[f116,f23])).

fof(f116,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | r2_hidden(sK6(sK3,X5,X4),X5)
      | ~ r2_hidden(X4,k9_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f95,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | r2_hidden(sK6(sK3,X0,X1),X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f56,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(sK6(sK3,X17,X18),X17)
      | ~ r2_hidden(X18,k9_relat_1(sK3,X17)) ) ),
    inference(resolution,[],[f21,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f198,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    inference(resolution,[],[f190,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f190,plain,(
    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),k1_funct_1(sK3,sK6(sK3,sK2,sK4))),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f177,f60])).

fof(f60,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f177,plain,(
    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),k1_funct_1(sK3,sK6(sK3,sK2,sK4))),sK3) ),
    inference(resolution,[],[f166,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    inference(resolution,[],[f118,f23])).

fof(f118,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ r2_hidden(X3,k1_relat_1(sK3))
      | r2_hidden(k4_tarski(X3,k1_funct_1(sK3,X3)),sK3) ) ),
    inference(resolution,[],[f96,f33])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f58,f24])).

fof(f58,plain,(
    ! [X21] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(X21,k1_relat_1(sK3))
      | r2_hidden(k4_tarski(X21,k1_funct_1(sK3,X21)),sK3) ) ),
    inference(resolution,[],[f21,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f166,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    inference(resolution,[],[f160,f62])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | r2_hidden(sK6(sK3,X0,X1),k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f159,f23])).

fof(f159,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | r2_hidden(sK6(sK3,X5,X4),k1_relat_1(sK3))
      | ~ r2_hidden(X4,k9_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f97,f33])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | r2_hidden(sK6(sK3,X0,X1),k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f57,f24])).

fof(f57,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(sK6(sK3,X19,X20),k1_relat_1(sK3))
      | ~ r2_hidden(X20,k9_relat_1(sK3,X19)) ) ),
    inference(resolution,[],[f21,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f235,plain,(
    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(resolution,[],[f229,f62])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1 ) ),
    inference(resolution,[],[f225,f23])).

fof(f225,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_funct_1(sK3,sK6(sK3,X5,X4)) = X4
      | ~ r2_hidden(X4,k9_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f98,f33])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f55,f24])).

fof(f55,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(sK3)
      | k1_funct_1(sK3,sK6(sK3,X15,X16)) = X16
      | ~ r2_hidden(X16,k9_relat_1(sK3,X15)) ) ),
    inference(resolution,[],[f21,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:30:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (12607)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (12613)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (12605)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (12615)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (12606)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (12614)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (12603)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (12615)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (12612)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f235,f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 0.21/0.49    inference(resolution,[],[f198,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ~r2_hidden(sK6(sK3,sK2,sK4),sK0) | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 0.21/0.49    inference(resolution,[],[f125,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r2_hidden(sK6(sK3,sK2,sK4),sK2)),
% 0.21/0.49    inference(resolution,[],[f119,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f20,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) )),
% 0.21/0.49    inference(resolution,[],[f23,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | r2_hidden(sK6(sK3,X0,X1),X0)) )),
% 0.21/0.49    inference(resolution,[],[f116,f23])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | r2_hidden(sK6(sK3,X5,X4),X5) | ~r2_hidden(X4,k9_relat_1(sK3,X5))) )),
% 0.21/0.49    inference(resolution,[],[f95,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | r2_hidden(sK6(sK3,X0,X1),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) )),
% 0.21/0.49    inference(resolution,[],[f56,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X17,X18] : (~v1_relat_1(sK3) | r2_hidden(sK6(sK3,X17,X18),X17) | ~r2_hidden(X18,k9_relat_1(sK3,X17))) )),
% 0.21/0.49    inference(resolution,[],[f21,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 0.21/0.49    inference(resolution,[],[f190,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),k1_funct_1(sK3,sK6(sK3,sK2,sK4))),k2_zfmisc_1(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f177,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.49    inference(resolution,[],[f23,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),k1_funct_1(sK3,sK6(sK3,sK2,sK4))),sK3)),
% 0.21/0.49    inference(resolution,[],[f166,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)) )),
% 0.21/0.49    inference(resolution,[],[f118,f23])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r2_hidden(X3,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X3,k1_funct_1(sK3,X3)),sK3)) )),
% 0.21/0.49    inference(resolution,[],[f96,f33])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(resolution,[],[f58,f24])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X21] : (~v1_relat_1(sK3) | ~r2_hidden(X21,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X21,k1_funct_1(sK3,X21)),sK3)) )),
% 0.21/0.49    inference(resolution,[],[f21,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f160,f62])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | r2_hidden(sK6(sK3,X0,X1),k1_relat_1(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f159,f23])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | r2_hidden(sK6(sK3,X5,X4),k1_relat_1(sK3)) | ~r2_hidden(X4,k9_relat_1(sK3,X5))) )),
% 0.21/0.49    inference(resolution,[],[f97,f33])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | r2_hidden(sK6(sK3,X0,X1),k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) )),
% 0.21/0.49    inference(resolution,[],[f57,f24])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X19,X20] : (~v1_relat_1(sK3) | r2_hidden(sK6(sK3,X19,X20),k1_relat_1(sK3)) | ~r2_hidden(X20,k9_relat_1(sK3,X19))) )),
% 0.21/0.49    inference(resolution,[],[f21,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 0.21/0.49    inference(resolution,[],[f229,f62])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1) )),
% 0.21/0.49    inference(resolution,[],[f225,f23])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_funct_1(sK3,sK6(sK3,X5,X4)) = X4 | ~r2_hidden(X4,k9_relat_1(sK3,X5))) )),
% 0.21/0.49    inference(resolution,[],[f98,f33])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) )),
% 0.21/0.49    inference(resolution,[],[f55,f24])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X15,X16] : (~v1_relat_1(sK3) | k1_funct_1(sK3,sK6(sK3,X15,X16)) = X16 | ~r2_hidden(X16,k9_relat_1(sK3,X15))) )),
% 0.21/0.49    inference(resolution,[],[f21,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (12615)------------------------------
% 0.21/0.49  % (12615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12615)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (12615)Memory used [KB]: 1791
% 0.21/0.49  % (12615)Time elapsed: 0.069 s
% 0.21/0.49  % (12615)------------------------------
% 0.21/0.49  % (12615)------------------------------
% 0.21/0.49  % (12599)Success in time 0.126 s
%------------------------------------------------------------------------------
