%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 110 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 259 expanded)
%              Number of equality atoms :   22 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f32])).

fof(f32,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f78,plain,(
    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f59,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f74,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f74,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f55,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f55,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f23,f52])).

fof(f52,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f49,plain,(
    v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f25,f23,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f59,plain,(
    r2_hidden(sK3(k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f43,f52])).

fof(f43,plain,(
    r2_hidden(sK3(k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),k7_relset_1(k1_xboole_0,sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ~ v1_xboole_0(k7_relset_1(k1_xboole_0,sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f24,f38])).

fof(f24,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:41:11 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.23/0.43  % (31652)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.23/0.43  % (31654)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.43  % (31652)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.43  % SZS output start Proof for theBenchmark
% 0.23/0.43  fof(f81,plain,(
% 0.23/0.43    $false),
% 0.23/0.43    inference(subsumption_resolution,[],[f78,f32])).
% 0.23/0.43  fof(f32,plain,(
% 0.23/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.43    inference(unit_resulting_resolution,[],[f25,f27])).
% 0.23/0.43  fof(f27,plain,(
% 0.23/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f20])).
% 0.23/0.43  fof(f20,plain,(
% 0.23/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.23/0.43  fof(f19,plain,(
% 0.23/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.23/0.43    introduced(choice_axiom,[])).
% 0.23/0.43  fof(f18,plain,(
% 0.23/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.43    inference(rectify,[],[f17])).
% 0.23/0.44  fof(f17,plain,(
% 0.23/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.44    inference(nnf_transformation,[],[f1])).
% 0.23/0.44  fof(f1,axiom,(
% 0.23/0.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    v1_xboole_0(k1_xboole_0)),
% 0.23/0.44    inference(cnf_transformation,[],[f2])).
% 0.23/0.44  fof(f2,axiom,(
% 0.23/0.44    v1_xboole_0(k1_xboole_0)),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.23/0.44  fof(f78,plain,(
% 0.23/0.44    r2_hidden(sK3(k1_xboole_0),k1_xboole_0)),
% 0.23/0.44    inference(backward_demodulation,[],[f59,f76])).
% 0.23/0.44  fof(f76,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) )),
% 0.23/0.44    inference(forward_demodulation,[],[f74,f26])).
% 0.23/0.44  fof(f26,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f4])).
% 0.23/0.44  fof(f4,axiom,(
% 0.23/0.44    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.23/0.44  fof(f74,plain,(
% 0.23/0.44    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) )),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f55,f31])).
% 0.23/0.44  fof(f31,plain,(
% 0.23/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f14])).
% 0.23/0.44  fof(f14,plain,(
% 0.23/0.44    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.44    inference(ennf_transformation,[],[f6])).
% 0.23/0.44  fof(f6,axiom,(
% 0.23/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.23/0.44  fof(f55,plain,(
% 0.23/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.44    inference(backward_demodulation,[],[f23,f52])).
% 0.23/0.44  fof(f52,plain,(
% 0.23/0.44    k1_xboole_0 = sK2),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f49,f38])).
% 0.23/0.44  fof(f38,plain,(
% 0.23/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.23/0.44    inference(resolution,[],[f29,f27])).
% 0.23/0.44  fof(f29,plain,(
% 0.23/0.44    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.44    inference(cnf_transformation,[],[f22])).
% 0.23/0.44  fof(f22,plain,(
% 0.23/0.44    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.23/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).
% 0.23/0.44  fof(f21,plain,(
% 0.23/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f12,plain,(
% 0.23/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.23/0.44    inference(ennf_transformation,[],[f3])).
% 0.23/0.44  fof(f3,axiom,(
% 0.23/0.44    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.23/0.44  fof(f49,plain,(
% 0.23/0.44    v1_xboole_0(sK2)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f25,f23,f30])).
% 0.23/0.44  fof(f30,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f13])).
% 0.23/0.44  fof(f13,plain,(
% 0.23/0.44    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.23/0.44    inference(ennf_transformation,[],[f5])).
% 0.23/0.44  fof(f5,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.23/0.44  fof(f23,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.44    inference(cnf_transformation,[],[f16])).
% 0.23/0.44  fof(f16,plain,(
% 0.23/0.44    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.23/0.44  fof(f15,plain,(
% 0.23/0.44    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f11,plain,(
% 0.23/0.44    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.23/0.44    inference(ennf_transformation,[],[f10])).
% 0.23/0.44  fof(f10,plain,(
% 0.23/0.44    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.44    inference(pure_predicate_removal,[],[f9])).
% 0.23/0.44  fof(f9,plain,(
% 0.23/0.44    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.44    inference(pure_predicate_removal,[],[f8])).
% 0.23/0.44  fof(f8,negated_conjecture,(
% 0.23/0.44    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.44    inference(negated_conjecture,[],[f7])).
% 0.23/0.44  fof(f7,conjecture,(
% 0.23/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.23/0.44  fof(f59,plain,(
% 0.23/0.44    r2_hidden(sK3(k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))),
% 0.23/0.44    inference(backward_demodulation,[],[f43,f52])).
% 0.23/0.44  fof(f43,plain,(
% 0.23/0.44    r2_hidden(sK3(k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),k7_relset_1(k1_xboole_0,sK0,sK2,sK1))),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f41,f28])).
% 0.23/0.44  fof(f28,plain,(
% 0.23/0.44    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f20])).
% 0.23/0.44  fof(f41,plain,(
% 0.23/0.44    ~v1_xboole_0(k7_relset_1(k1_xboole_0,sK0,sK2,sK1))),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f24,f38])).
% 0.23/0.44  fof(f24,plain,(
% 0.23/0.44    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.23/0.44    inference(cnf_transformation,[],[f16])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (31652)------------------------------
% 0.23/0.44  % (31652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (31652)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (31652)Memory used [KB]: 6140
% 0.23/0.44  % (31652)Time elapsed: 0.005 s
% 0.23/0.44  % (31652)------------------------------
% 0.23/0.44  % (31652)------------------------------
% 0.23/0.44  % (31649)Success in time 0.059 s
%------------------------------------------------------------------------------
