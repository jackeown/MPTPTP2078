%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  83 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 ( 439 expanded)
%              Number of equality atoms :   70 ( 134 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(subsumption_resolution,[],[f151,f24])).

fof(f24,plain,(
    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f151,plain,(
    sK2 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(resolution,[],[f109,f22])).

fof(f22,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f109,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f108,f71])).

fof(f71,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f37,f20])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f108,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f107,f21])).

fof(f21,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v2_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f102,f18])).

fof(f18,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_funct_1(sK3)
      | ~ v2_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1 ) ),
    inference(superposition,[],[f66,f86])).

fof(f86,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f77,f85])).

fof(f85,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f84,f19])).

fof(f19,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f83,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f44,f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f77,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f66,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f65,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (10087)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.42  % (10087)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f151,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1) & (r2_hidden(X2,X0) & v2_funct_1(X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    sK2 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))),
% 0.21/0.42    inference(resolution,[],[f109,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    r2_hidden(sK2,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f108,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    v1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f37,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_relat_1(sK3) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f107,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    v2_funct_1(sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f102,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    v1_funct_1(sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1) )),
% 0.21/0.42    inference(superposition,[],[f66,f86])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    sK0 = k1_relat_1(sK3)),
% 0.21/0.42    inference(backward_demodulation,[],[f77,f85])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f84,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.42    inference(subsumption_resolution,[],[f83,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    k1_xboole_0 != sK1),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.42    inference(resolution,[],[f44,f20])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(flattening,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f38,f20])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f65,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f51,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.42    inference(equality_resolution,[],[f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.42    inference(equality_resolution,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | k1_funct_1(X1,X2) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (10087)------------------------------
% 0.21/0.42  % (10087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (10087)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (10087)Memory used [KB]: 1663
% 0.21/0.42  % (10087)Time elapsed: 0.007 s
% 0.21/0.42  % (10087)------------------------------
% 0.21/0.42  % (10087)------------------------------
% 0.21/0.42  % (10069)Success in time 0.068 s
%------------------------------------------------------------------------------
