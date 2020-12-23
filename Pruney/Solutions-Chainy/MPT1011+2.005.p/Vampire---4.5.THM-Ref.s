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
% DateTime   : Thu Dec  3 13:05:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 186 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  176 (1034 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44,f34])).

fof(f34,plain,(
    sK1 = k1_funct_1(sK2,sK4(sK0,sK2,sK3)) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK1 = k1_funct_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f25,f16])).

fof(f16,plain,(
    v1_funct_2(sK2,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X2,X0,k1_tarski(X1))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(f25,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
      | sK1 = k1_funct_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f22,f15])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
      | sK1 = k1_funct_1(sK2,X1) ) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | k1_funct_1(X3,X2) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f33,plain,(
    r2_hidden(sK4(sK0,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f32,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f31,f13])).

fof(f13,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f30,f12])).

fof(f12,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f29,f11])).

fof(f11,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f28,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f27,f16])).

fof(f27,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X2,X3),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f44,plain,(
    sK1 != k1_funct_1(sK2,sK4(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f43,f35])).

fof(f35,plain,(
    sK1 = k1_funct_1(sK3,sK4(sK0,sK2,sK3)) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f23,f12])).

fof(f23,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f21,f11])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f20,f13])).

fof(f43,plain,(
    k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f42,f15])).

fof(f42,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f41,f13])).

fof(f41,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f40,f12])).

fof(f40,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f39,f11])).

fof(f39,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f38,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f37,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f19,f14])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (12555)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (12549)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.43  % (12549)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f44,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    sK1 = k1_funct_1(sK2,sK4(sK0,sK2,sK3))),
% 0.20/0.43    inference(resolution,[],[f33,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,sK0) | sK1 = k1_funct_1(sK2,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f25,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    v1_funct_2(sK2,sK0,k1_tarski(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2))),
% 0.20/0.43    inference(flattening,[],[f5])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.20/0.43    inference(negated_conjecture,[],[f3])).
% 0.20/0.43  fof(f3,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | sK1 = k1_funct_1(sK2,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f22,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    v1_funct_1(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | sK1 = k1_funct_1(sK2,X1)) )),
% 0.20/0.43    inference(resolution,[],[f20,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~r2_hidden(X2,X0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | k1_funct_1(X3,X2) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k1_funct_1(X3,X2) = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) = X1 | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3)))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    r2_hidden(sK4(sK0,sK2,sK3),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f32,f15])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f31,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f30,f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f29,f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    v1_funct_1(sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f28,f17])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f27,f16])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(resolution,[],[f18,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ~r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X2,X3),X0) | ~v1_funct_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.43    inference(flattening,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    sK1 != k1_funct_1(sK2,sK4(sK0,sK2,sK3))),
% 0.20/0.43    inference(forward_demodulation,[],[f43,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    sK1 = k1_funct_1(sK3,sK4(sK0,sK2,sK3))),
% 0.20/0.43    inference(resolution,[],[f33,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k1_funct_1(sK3,X0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f23,f12])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | sK1 = k1_funct_1(sK3,X0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f21,f11])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | sK1 = k1_funct_1(sK3,X0)) )),
% 0.20/0.43    inference(resolution,[],[f20,f13])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))),
% 0.20/0.43    inference(subsumption_resolution,[],[f42,f15])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f41,f13])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f40,f12])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f39,f11])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f38,f17])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f37,f16])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~v1_funct_1(sK2)),
% 0.20/0.43    inference(resolution,[],[f19,f14])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) | ~v1_funct_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (12549)------------------------------
% 0.20/0.43  % (12549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (12549)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (12549)Memory used [KB]: 10618
% 0.20/0.43  % (12549)Time elapsed: 0.006 s
% 0.20/0.43  % (12549)------------------------------
% 0.20/0.43  % (12549)------------------------------
% 0.20/0.43  % (12557)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.43  % (12548)Success in time 0.075 s
%------------------------------------------------------------------------------
