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
% DateTime   : Thu Dec  3 13:06:19 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 143 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 621 expanded)
%              Number of equality atoms :   25 ( 101 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f75,f65,f66,f20])).

fof(f20,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f66,plain,(
    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f22,f56,f61,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f61,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f21,f54])).

fof(f54,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f39,f24,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK2) ),
    inference(unit_resulting_resolution,[],[f22,f56,f61,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    inference(unit_resulting_resolution,[],[f69,f64,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f22,f56,f61,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f62,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f52,plain,(
    m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:58:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (13356)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (13353)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (13350)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (13359)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.53  % (13354)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (13364)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.54  % (13368)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.54  % (13354)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f98,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f75,f65,f66,f20])).
% 1.29/0.54  fof(f20,plain,(
% 1.29/0.54    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f12,plain,(
% 1.29/0.54    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.29/0.54    inference(flattening,[],[f11])).
% 1.29/0.54  fof(f11,plain,(
% 1.29/0.54    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.29/0.54    inference(ennf_transformation,[],[f10])).
% 1.29/0.54  fof(f10,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.29/0.54    inference(negated_conjecture,[],[f9])).
% 1.29/0.54  fof(f9,conjecture,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 1.29/0.54  fof(f66,plain,(
% 1.29/0.54    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f22,f56,f61,f45])).
% 1.29/0.54  fof(f45,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.29/0.54    inference(equality_resolution,[],[f33])).
% 1.29/0.54  fof(f33,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f16])).
% 1.29/0.54  fof(f16,plain,(
% 1.29/0.54    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.29/0.54    inference(flattening,[],[f15])).
% 1.29/0.54  fof(f15,plain,(
% 1.29/0.54    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.29/0.54    inference(ennf_transformation,[],[f5])).
% 1.29/0.54  fof(f5,axiom,(
% 1.29/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.29/0.54  fof(f61,plain,(
% 1.29/0.54    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.29/0.54    inference(backward_demodulation,[],[f21,f54])).
% 1.29/0.54  fof(f54,plain,(
% 1.29/0.54    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) )),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f24,f25])).
% 1.29/0.54  fof(f25,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f13])).
% 1.29/0.54  fof(f13,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f56,plain,(
% 1.29/0.54    v1_relat_1(sK3)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f39,f24,f38])).
% 1.29/0.54  fof(f38,plain,(
% 1.29/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f18])).
% 1.29/0.54  fof(f18,plain,(
% 1.29/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.29/0.54    inference(ennf_transformation,[],[f3])).
% 1.29/0.54  fof(f3,axiom,(
% 1.29/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.29/0.54  fof(f39,plain,(
% 1.29/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    v1_funct_1(sK3)),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f65,plain,(
% 1.29/0.54    r2_hidden(sK6(sK3,sK2,sK4),sK2)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f22,f56,f61,f46])).
% 1.29/0.54  fof(f46,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.29/0.54    inference(equality_resolution,[],[f32])).
% 1.29/0.54  fof(f32,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f16])).
% 1.29/0.54  fof(f75,plain,(
% 1.29/0.54    r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f69,f64,f35])).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f17])).
% 1.29/0.54  fof(f17,plain,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.54    inference(ennf_transformation,[],[f1])).
% 1.29/0.54  fof(f1,axiom,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.54  fof(f64,plain,(
% 1.29/0.54    r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f22,f56,f61,f47])).
% 1.29/0.54  fof(f47,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.29/0.54    inference(equality_resolution,[],[f31])).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f16])).
% 1.29/0.54  fof(f69,plain,(
% 1.29/0.54    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f62,f42])).
% 1.29/0.54  fof(f42,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.54  fof(f62,plain,(
% 1.29/0.54    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))),
% 1.29/0.54    inference(forward_demodulation,[],[f52,f53])).
% 1.29/0.54  fof(f53,plain,(
% 1.29/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f24,f26])).
% 1.29/0.54  fof(f26,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f14])).
% 1.29/0.54  fof(f14,plain,(
% 1.29/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f7])).
% 1.29/0.54  fof(f7,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.29/0.54  fof(f52,plain,(
% 1.29/0.54    m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f24,f40])).
% 1.29/0.54  fof(f40,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f19])).
% 1.29/0.54  fof(f19,plain,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f6])).
% 1.29/0.54  fof(f6,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (13354)------------------------------
% 1.29/0.54  % (13354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (13354)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (13354)Memory used [KB]: 6268
% 1.29/0.54  % (13354)Time elapsed: 0.125 s
% 1.29/0.54  % (13354)------------------------------
% 1.29/0.54  % (13354)------------------------------
% 1.29/0.54  % (13349)Success in time 0.177 s
%------------------------------------------------------------------------------
