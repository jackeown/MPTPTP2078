%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 881 expanded)
%              Number of leaves         :   13 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  204 (3541 expanded)
%              Number of equality atoms :   66 ( 939 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(global_subsumption,[],[f457,f516])).

fof(f516,plain,(
    k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f477,f500])).

% (26281)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f500,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f33,f499])).

fof(f499,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f472,f452])).

fof(f452,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f337,f451])).

fof(f451,plain,
    ( ~ r2_hidden(sK3(sK8(sK1,k2_relat_1(sK2))),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f441,f423])).

fof(f423,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f30,f422])).

fof(f422,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f420,f244])).

% (26288)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f244,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f31,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f31,plain,(
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

fof(f420,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f441,plain,(
    ~ r2_hidden(sK3(sK8(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f274,f369,f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f65,f28])).

fof(f28,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f369,plain,(
    ~ sP5(sK8(sK1,k2_relat_1(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f79,f29,f273,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f273,plain,(
    ~ r2_hidden(sK8(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f260,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f260,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f163,f252,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f252,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f31,f250])).

fof(f250,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f32,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f163,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f160,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f160,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f31,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f44,f31,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f274,plain,(
    r2_hidden(sK8(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f260,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f337,plain,(
    r2_hidden(sK3(sK8(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f274,f27])).

fof(f27,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f472,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(backward_demodulation,[],[f214,f452])).

fof(f214,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f170,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f51,f43])).

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

fof(f170,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f163,f49])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f477,plain,(
    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f249,f452])).

fof(f249,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f31,f54])).

% (26287)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f457,plain,(
    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f32,f452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.54  % (26284)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (26300)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (26291)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (26292)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (26283)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (26285)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (26301)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (26294)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (26302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.60  % (26282)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.60  % (26302)Refutation found. Thanks to Tanya!
% 0.22/0.60  % SZS status Theorem for theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f517,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(global_subsumption,[],[f457,f516])).
% 0.22/0.60  fof(f516,plain,(
% 0.22/0.60    k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.60    inference(forward_demodulation,[],[f477,f500])).
% 0.22/0.60  % (26281)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.60  fof(f500,plain,(
% 0.22/0.60    k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.60    inference(global_subsumption,[],[f33,f499])).
% 0.22/0.60  fof(f499,plain,(
% 0.22/0.60    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.60    inference(forward_demodulation,[],[f472,f452])).
% 0.22/0.60  fof(f452,plain,(
% 0.22/0.60    k1_xboole_0 = sK1),
% 0.22/0.60    inference(global_subsumption,[],[f337,f451])).
% 0.22/0.60  fof(f451,plain,(
% 0.22/0.60    ~r2_hidden(sK3(sK8(sK1,k2_relat_1(sK2))),sK0) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(superposition,[],[f441,f423])).
% 0.22/0.60  fof(f423,plain,(
% 0.22/0.60    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(global_subsumption,[],[f30,f422])).
% 0.22/0.60  fof(f422,plain,(
% 0.22/0.60    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.60    inference(forward_demodulation,[],[f420,f244])).
% 0.22/0.60  % (26288)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.60  fof(f244,plain,(
% 0.22/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f31,f53])).
% 0.22/0.60  fof(f53,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(ennf_transformation,[],[f10])).
% 0.22/0.60  fof(f10,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.60    inference(flattening,[],[f15])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.60    inference(ennf_transformation,[],[f14])).
% 0.22/0.60  fof(f14,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.60    inference(negated_conjecture,[],[f13])).
% 0.22/0.60  fof(f13,conjecture,(
% 0.22/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.60  fof(f420,plain,(
% 0.22/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.60    inference(resolution,[],[f62,f31])).
% 0.22/0.60  fof(f62,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(flattening,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(ennf_transformation,[],[f12])).
% 0.22/0.60  fof(f12,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f441,plain,(
% 0.22/0.60    ~r2_hidden(sK3(sK8(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f274,f369,f176])).
% 0.22/0.60  fof(f176,plain,(
% 0.22/0.60    ( ! [X0] : (~r2_hidden(sK3(X0),k1_relat_1(sK2)) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.60    inference(superposition,[],[f65,f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f65,plain,(
% 0.22/0.60    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.22/0.60    inference(equality_resolution,[],[f35])).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f19])).
% 0.22/0.60  fof(f19,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(flattening,[],[f18])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,axiom,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.60  fof(f369,plain,(
% 0.22/0.60    ~sP5(sK8(sK1,k2_relat_1(sK2)),sK2)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f79,f29,f273,f64])).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(equality_resolution,[],[f38])).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f19])).
% 0.22/0.60  fof(f273,plain,(
% 0.22/0.60    ~r2_hidden(sK8(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f260,f52])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.60  fof(f260,plain,(
% 0.22/0.60    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f163,f252,f49])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.60  fof(f252,plain,(
% 0.22/0.60    sK1 != k2_relat_1(sK2)),
% 0.22/0.60    inference(global_subsumption,[],[f31,f250])).
% 0.22/0.60  fof(f250,plain,(
% 0.22/0.60    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.60    inference(superposition,[],[f32,f54])).
% 0.22/0.60  fof(f54,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f23])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(ennf_transformation,[],[f11])).
% 0.22/0.60  fof(f11,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f163,plain,(
% 0.22/0.60    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f79,f160,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.60    inference(ennf_transformation,[],[f6])).
% 0.22/0.60  fof(f6,axiom,(
% 0.22/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.60  fof(f160,plain,(
% 0.22/0.60    v5_relat_1(sK2,sK1)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f31,f56])).
% 0.22/0.60  fof(f56,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(ennf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    v1_funct_1(sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f79,plain,(
% 0.22/0.60    v1_relat_1(sK2)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f44,f31,f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,axiom,(
% 0.22/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.60  fof(f274,plain,(
% 0.22/0.60    r2_hidden(sK8(sK1,k2_relat_1(sK2)),sK1)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f260,f51])).
% 0.22/0.60  fof(f51,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f21])).
% 0.22/0.60  fof(f337,plain,(
% 0.22/0.60    r2_hidden(sK3(sK8(sK1,k2_relat_1(sK2))),sK0)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f274,f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f472,plain,(
% 0.22/0.60    k1_xboole_0 = k2_relat_1(sK2) | ~v1_xboole_0(sK1)),
% 0.22/0.60    inference(backward_demodulation,[],[f214,f452])).
% 0.22/0.60  fof(f214,plain,(
% 0.22/0.60    sK1 = k2_relat_1(sK2) | ~v1_xboole_0(sK1)),
% 0.22/0.60    inference(resolution,[],[f170,f82])).
% 0.22/0.60  fof(f82,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.60    inference(resolution,[],[f51,f43])).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.60  fof(f170,plain,(
% 0.22/0.60    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f163,f49])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    v1_xboole_0(k1_xboole_0)),
% 0.22/0.60    inference(cnf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    v1_xboole_0(k1_xboole_0)),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.60  fof(f477,plain,(
% 0.22/0.60    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.60    inference(backward_demodulation,[],[f249,f452])).
% 0.22/0.60  fof(f249,plain,(
% 0.22/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f31,f54])).
% 0.22/0.60  % (26287)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  fof(f457,plain,(
% 0.22/0.60    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.60    inference(backward_demodulation,[],[f32,f452])).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (26302)------------------------------
% 0.22/0.60  % (26302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (26302)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (26302)Memory used [KB]: 6524
% 0.22/0.60  % (26302)Time elapsed: 0.161 s
% 0.22/0.60  % (26302)------------------------------
% 0.22/0.60  % (26302)------------------------------
% 0.22/0.60  % (26276)Success in time 0.229 s
%------------------------------------------------------------------------------
