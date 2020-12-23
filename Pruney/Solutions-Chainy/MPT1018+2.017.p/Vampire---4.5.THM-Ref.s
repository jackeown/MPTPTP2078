%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 249 expanded)
%              Number of leaves         :    7 (  48 expanded)
%              Depth                    :   22
%              Number of atoms          :  218 (1275 expanded)
%              Number of equality atoms :   58 ( 299 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(subsumption_resolution,[],[f273,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f273,plain,(
    ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f267,f91])).

fof(f91,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f89,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f267,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f266,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f266,plain,(
    ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f262,f22])).

fof(f22,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f262,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f253,f261])).

fof(f261,plain,(
    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f260,f23])).

fof(f260,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f254,f91])).

fof(f254,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f251,f29])).

fof(f251,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(resolution,[],[f169,f19])).

fof(f19,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f169,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK0)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9 ) ),
    inference(subsumption_resolution,[],[f168,f92])).

fof(f92,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f91,f52])).

fof(f52,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f168,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK0)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9 ) ),
    inference(subsumption_resolution,[],[f167,f26])).

fof(f26,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f167,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK0)
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9 ) ),
    inference(subsumption_resolution,[],[f166,f23])).

fof(f166,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9 ) ),
    inference(subsumption_resolution,[],[f151,f91])).

fof(f151,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK0)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9 ) ),
    inference(superposition,[],[f49,f90])).

fof(f90,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f88,f85])).

fof(f85,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f84,f25])).

fof(f84,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f83,f23])).

fof(f83,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f24,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f24,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f25,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | k1_funct_1(X1,X2) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f253,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f252,f21])).

fof(f21,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f252,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) ),
    inference(resolution,[],[f169,f20])).

fof(f20,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:19:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (785)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (785)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f274,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f273,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    v1_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.46  fof(f273,plain,(
% 0.21/0.46    ~v1_funct_1(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f267,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f89,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 0.21/0.46    inference(resolution,[],[f25,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f267,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.46    inference(resolution,[],[f266,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    ~v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f262,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    sK2 != sK3),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    sK2 = sK3 | ~v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.46    inference(backward_demodulation,[],[f253,f261])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f260,f23])).
% 0.21/0.46  fof(f260,plain,(
% 0.21/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_funct_1(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f254,f91])).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.46    inference(resolution,[],[f251,f29])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    ~v1_funct_1(k2_funct_1(sK1)) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f169,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    r2_hidden(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    ( ! [X9] : (~r2_hidden(X9,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f168,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.46    inference(resolution,[],[f91,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.46    inference(resolution,[],[f23,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    ( ! [X9] : (~r2_hidden(X9,sK0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f167,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    v2_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f167,plain,(
% 0.21/0.46    ( ! [X9] : (~r2_hidden(X9,sK0) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f166,f23])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ( ! [X9] : (~r2_hidden(X9,sK0) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f151,f91])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    ( ! [X9] : (~r2_hidden(X9,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X9)) = X9) )),
% 0.21/0.46    inference(superposition,[],[f49,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1)),
% 0.21/0.46    inference(forward_demodulation,[],[f88,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f84,f25])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f83,f23])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    inference(resolution,[],[f24,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    inference(resolution,[],[f25,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.46    inference(equality_resolution,[],[f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.46    inference(equality_resolution,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | k1_funct_1(X1,X2) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.46    inference(forward_demodulation,[],[f252,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    ~v1_funct_1(k2_funct_1(sK1)) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))),
% 0.21/0.46    inference(resolution,[],[f169,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (785)------------------------------
% 0.21/0.46  % (785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (785)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (785)Memory used [KB]: 1663
% 0.21/0.46  % (785)Time elapsed: 0.009 s
% 0.21/0.46  % (785)------------------------------
% 0.21/0.46  % (785)------------------------------
% 0.21/0.47  % (765)Success in time 0.101 s
%------------------------------------------------------------------------------
