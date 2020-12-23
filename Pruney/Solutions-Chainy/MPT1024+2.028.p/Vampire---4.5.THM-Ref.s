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
% DateTime   : Thu Dec  3 13:06:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 145 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 590 expanded)
%              Number of equality atoms :   22 (  95 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f64])).

fof(f64,plain,(
    ~ r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f53,f63])).

fof(f63,plain,(
    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f62,f41])).

fof(f41,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
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
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f57,f20])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f51,plain,(
    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f50,f41])).

fof(f50,plain,
    ( r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f19,f44])).

fof(f44,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f19,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X3),X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f53,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    inference(resolution,[],[f49,f18])).

fof(f18,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK2) ),
    inference(subsumption_resolution,[],[f47,f41])).

fof(f47,plain,
    ( r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f59,plain,(
    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (4961)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.42  % (4961)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f77,f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ~r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 0.21/0.42    inference(subsumption_resolution,[],[f53,f63])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 0.21/0.42    inference(subsumption_resolution,[],[f62,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    v1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f29,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.42    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f57,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    v1_funct_1(sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f51,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f50,f41])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f39,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.42    inference(backward_demodulation,[],[f19,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.21/0.42    inference(resolution,[],[f33,f21])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X3),X3),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(equality_resolution,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK6(X0,X1,X3),X3),X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ~r2_hidden(sK6(sK3,sK2,sK4),sK0) | sK4 != k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 0.21/0.42    inference(resolution,[],[f49,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    r2_hidden(sK6(sK3,sK2,sK4),sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f47,f41])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    r2_hidden(sK6(sK3,sK2,sK4),sK2) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f46,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | r2_hidden(sK6(X0,X1,X3),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(equality_resolution,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 0.21/0.42    inference(resolution,[],[f59,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1))),
% 0.21/0.42    inference(resolution,[],[f51,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.42    inference(resolution,[],[f28,f21])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (4961)------------------------------
% 0.21/0.42  % (4961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (4961)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (4961)Memory used [KB]: 1663
% 0.21/0.42  % (4961)Time elapsed: 0.006 s
% 0.21/0.42  % (4961)------------------------------
% 0.21/0.42  % (4961)------------------------------
% 0.21/0.42  % (4942)Success in time 0.064 s
%------------------------------------------------------------------------------
