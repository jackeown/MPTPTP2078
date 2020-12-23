%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:37 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 225 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  204 (1085 expanded)
%              Number of equality atoms :   49 ( 217 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f108])).

fof(f108,plain,(
    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f71,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f106,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(backward_demodulation,[],[f57,f74])).

fof(f74,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f68,f62])).

fof(f62,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f61,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(resolution,[],[f131,f83])).

fof(f83,plain,(
    ! [X1] :
      ( m1_subset_1(X1,sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f73,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f73,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f66,f67])).

fof(f67,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f66,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f131,plain,(
    ~ m1_subset_1(k1_funct_1(sK3,sK2),sK1) ),
    inference(subsumption_resolution,[],[f128,f73])).

fof(f128,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,sK2),sK1) ),
    inference(resolution,[],[f109,f63])).

fof(f63,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_funct_1(sK3,sK2),sK1) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

% (30805)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f36,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f108,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:08:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (30799)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.46  % (30799)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f139,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(subsumption_resolution,[],[f137,f108])).
% 0.18/0.46  fof(f108,plain,(
% 0.18/0.46    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.18/0.46    inference(subsumption_resolution,[],[f106,f76])).
% 0.18/0.46  fof(f76,plain,(
% 0.18/0.46    v1_relat_1(sK3)),
% 0.18/0.46    inference(subsumption_resolution,[],[f71,f38])).
% 0.18/0.46  fof(f38,plain,(
% 0.18/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.46  fof(f71,plain,(
% 0.18/0.46    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.18/0.46    inference(resolution,[],[f33,f37])).
% 0.18/0.46  fof(f37,plain,(
% 0.18/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.46  fof(f33,plain,(
% 0.18/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28])).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.18/0.46    inference(flattening,[],[f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.18/0.46    inference(ennf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,negated_conjecture,(
% 0.18/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.18/0.46    inference(negated_conjecture,[],[f11])).
% 0.18/0.46  fof(f11,conjecture,(
% 0.18/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.18/0.46  fof(f106,plain,(
% 0.18/0.46    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.18/0.46    inference(resolution,[],[f75,f34])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    r2_hidden(sK2,sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f75,plain,(
% 0.18/0.46    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.18/0.46    inference(backward_demodulation,[],[f57,f74])).
% 0.18/0.46  fof(f74,plain,(
% 0.18/0.46    sK0 = k1_relat_1(sK3)),
% 0.18/0.46    inference(forward_demodulation,[],[f68,f62])).
% 0.18/0.46  fof(f62,plain,(
% 0.18/0.46    sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.18/0.46    inference(subsumption_resolution,[],[f61,f33])).
% 0.18/0.46  fof(f61,plain,(
% 0.18/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.46    inference(subsumption_resolution,[],[f60,f35])).
% 0.18/0.46  fof(f35,plain,(
% 0.18/0.46    k1_xboole_0 != sK1),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f60,plain,(
% 0.18/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.46    inference(resolution,[],[f32,f44])).
% 0.18/0.46  fof(f44,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f30])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(nnf_transformation,[],[f24])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(flattening,[],[f23])).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f10])).
% 0.18/0.46  fof(f10,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.18/0.46  fof(f32,plain,(
% 0.18/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f68,plain,(
% 0.18/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.18/0.46    inference(resolution,[],[f33,f41])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.46  fof(f57,plain,(
% 0.18/0.46    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.18/0.46    inference(resolution,[],[f31,f40])).
% 0.18/0.46  fof(f40,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.18/0.46    inference(flattening,[],[f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.18/0.46    inference(ennf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    v1_funct_1(sK3)),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f137,plain,(
% 0.18/0.46    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.18/0.46    inference(resolution,[],[f131,f83])).
% 0.18/0.46  fof(f83,plain,(
% 0.18/0.46    ( ! [X1] : (m1_subset_1(X1,sK1) | ~r2_hidden(X1,k2_relat_1(sK3))) )),
% 0.18/0.46    inference(resolution,[],[f73,f50])).
% 0.18/0.46  fof(f50,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f26])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.18/0.46    inference(flattening,[],[f25])).
% 0.18/0.46  fof(f25,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.18/0.46    inference(ennf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.18/0.46  fof(f73,plain,(
% 0.18/0.46    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.18/0.46    inference(backward_demodulation,[],[f66,f67])).
% 0.18/0.46  fof(f67,plain,(
% 0.18/0.46    k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)),
% 0.18/0.46    inference(resolution,[],[f33,f42])).
% 0.18/0.46  fof(f42,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f21])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f9])).
% 0.18/0.46  fof(f9,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.46  fof(f66,plain,(
% 0.18/0.46    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))),
% 0.18/0.46    inference(resolution,[],[f33,f43])).
% 0.18/0.46  fof(f43,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.18/0.46  fof(f131,plain,(
% 0.18/0.46    ~m1_subset_1(k1_funct_1(sK3,sK2),sK1)),
% 0.18/0.46    inference(subsumption_resolution,[],[f128,f73])).
% 0.18/0.46  fof(f128,plain,(
% 0.18/0.46    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_funct_1(sK3,sK2),sK1)),
% 0.18/0.46    inference(resolution,[],[f109,f63])).
% 0.18/0.46  fof(f63,plain,(
% 0.18/0.46    v1_xboole_0(sK1) | ~m1_subset_1(k1_funct_1(sK3,sK2),sK1)),
% 0.18/0.46    inference(resolution,[],[f36,f39])).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f17])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.18/0.46    inference(flattening,[],[f16])).
% 0.18/0.46  % (30805)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.18/0.46  fof(f36,plain,(
% 0.18/0.46    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f109,plain,(
% 0.18/0.46    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0))) )),
% 0.18/0.46    inference(resolution,[],[f108,f51])).
% 0.18/0.46  fof(f51,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f27])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (30799)------------------------------
% 0.18/0.46  % (30799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (30799)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (30799)Memory used [KB]: 1663
% 0.18/0.46  % (30799)Time elapsed: 0.056 s
% 0.18/0.46  % (30799)------------------------------
% 0.18/0.46  % (30799)------------------------------
% 0.18/0.46  % (30810)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.46  % (30794)Success in time 0.115 s
%------------------------------------------------------------------------------
