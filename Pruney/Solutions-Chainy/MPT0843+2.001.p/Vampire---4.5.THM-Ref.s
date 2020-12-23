%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 303 expanded)
%              Number of leaves         :    6 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  133 (1092 expanded)
%              Number of equality atoms :    6 ( 138 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(global_subsumption,[],[f79,f109,f192])).

fof(f192,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) ),
    inference(resolution,[],[f137,f105])).

fof(f105,plain,(
    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f17,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ! [X3] :
                  ( r2_hidden(X3,X0)
                 => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(f104,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f84,f91])).

fof(f91,plain,(
    k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)) ),
    inference(resolution,[],[f86,f14])).

fof(f14,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f85,f26])).

fof(f26,plain,(
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

fof(f85,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0)) ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f48,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,k2_zfmisc_1(sK0,sK0)) ) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,k2_zfmisc_1(sK0,sK0)) ) ),
    inference(resolution,[],[f15,f29])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f72,f16])).

fof(f16,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(resolution,[],[f44,f15])).

fof(f44,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0)
      | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1)
      | r2_relset_1(sK0,sK0,sK1,X0) ) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f15,f30])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f25])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
      | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X0),sK2) ) ),
    inference(subsumption_resolution,[],[f136,f35])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X0),sK2) ) ),
    inference(superposition,[],[f24,f91])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f109,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f106,f43])).

fof(f106,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f105,f24])).

fof(f79,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f76,f16])).

fof(f76,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)
    | r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(resolution,[],[f45,f15])).

fof(f45,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X1),sK4(sK0,sK0,sK1,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X1),sK4(sK0,sK0,sK1,X1)),sK1)
      | r2_relset_1(sK0,sK0,sK1,X1) ) ),
    inference(resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (29199)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (29207)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (29207)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f79,f109,f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2)),
% 0.21/0.51    inference(resolution,[],[f137,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f17,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f93,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2)))),
% 0.21/0.52    inference(backward_demodulation,[],[f84,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)) = k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))),
% 0.21/0.52    inference(resolution,[],[f86,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,sK0) | k11_relat_1(sK1,X3) = k11_relat_1(sK2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    r2_hidden(sK3(sK0,sK0,sK1,sK2),sK0)),
% 0.21/0.52    inference(resolution,[],[f85,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK1) | r2_hidden(X4,k2_zfmisc_1(sK0,sK0))) )),
% 0.21/0.52    inference(resolution,[],[f17,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f75,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(X4,k2_zfmisc_1(sK0,sK0))) )),
% 0.21/0.52    inference(resolution,[],[f15,f29])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f72,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f44,f15])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),X0) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X0),sK4(sK0,sK0,sK1,X0)),sK1) | r2_relset_1(sK0,sK0,sK1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f17,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f15,f30])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_hidden(sK4(sK0,sK0,sK1,sK2),k11_relat_1(sK2,sK3(sK0,sK0,sK1,sK2))) | ~v1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f75,f25])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X0),sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f136,f35])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK3(sK0,sK0,sK1,sK2))) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),X0),sK2)) )),
% 0.21/0.52    inference(superposition,[],[f24,f91])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f43])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)),
% 0.21/0.52    inference(resolution,[],[f105,f24])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f16])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK2) | ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,sK2),sK4(sK0,sK0,sK1,sK2)),sK1) | r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f45,f15])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X1),sK4(sK0,sK0,sK1,X1)),X1) | ~r2_hidden(k4_tarski(sK3(sK0,sK0,sK1,X1),sK4(sK0,sK0,sK1,X1)),sK1) | r2_relset_1(sK0,sK0,sK1,X1)) )),
% 0.21/0.52    inference(resolution,[],[f17,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2,X3),sK4(X0,X1,X2,X3)),X2) | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (29207)------------------------------
% 0.21/0.52  % (29207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29207)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (29207)Memory used [KB]: 6396
% 0.21/0.52  % (29207)Time elapsed: 0.085 s
% 0.21/0.52  % (29207)------------------------------
% 0.21/0.52  % (29207)------------------------------
% 0.21/0.52  % (29186)Success in time 0.16 s
%------------------------------------------------------------------------------
