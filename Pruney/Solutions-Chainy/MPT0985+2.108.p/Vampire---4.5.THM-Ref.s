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
% DateTime   : Thu Dec  3 13:02:16 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  198 (14152 expanded)
%              Number of leaves         :   23 (3453 expanded)
%              Depth                    :   35
%              Number of atoms          :  517 (82411 expanded)
%              Number of equality atoms :  166 (12031 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f841,plain,(
    $false ),
    inference(subsumption_resolution,[],[f840,f683])).

fof(f683,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f100,f682])).

fof(f682,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f681,f167])).

fof(f167,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f681,plain,(
    sK3 = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f610,f171])).

fof(f171,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f610,plain,(
    sK3 = k3_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f233,f596])).

fof(f596,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f595,f213])).

fof(f213,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f102,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f102,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f87])).

% (26734)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f87,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f44])).

fof(f44,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f595,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f591,f207])).

fof(f207,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f196,f100])).

fof(f196,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f103,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f103,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f591,plain,
    ( ~ v1_funct_1(k4_relat_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f582,f556])).

fof(f556,plain,(
    v1_funct_2(k4_relat_1(sK3),sK2,sK1) ),
    inference(subsumption_resolution,[],[f555,f213])).

fof(f555,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f553,f207])).

fof(f553,plain,
    ( ~ v1_funct_1(k4_relat_1(sK3))
    | v1_funct_2(k4_relat_1(sK3),sK2,sK1) ),
    inference(subsumption_resolution,[],[f550,f452])).

fof(f452,plain,(
    v1_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f446,f135])).

fof(f446,plain,(
    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f445,f213])).

fof(f445,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f284,f206])).

fof(f206,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f195,f100])).

fof(f195,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f103,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f284,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f283,f229])).

fof(f229,plain,(
    sK2 = k1_relat_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f225,f217])).

fof(f217,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f210,f104])).

fof(f104,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f210,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f102,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f225,plain,(
    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f213,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f283,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3))))
    | ~ v1_relat_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f282,f226])).

% (26722)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f226,plain,(
    k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f213,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f282,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k2_relat_1(k4_relat_1(sK3)))))
    | ~ v1_relat_1(k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f275,f213])).

fof(f275,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k2_relat_1(k4_relat_1(sK3)))))
    | ~ v1_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f207,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f550,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f366,f402])).

fof(f402,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(forward_demodulation,[],[f399,f389])).

fof(f389,plain,(
    k1_relat_1(sK3) = k10_relat_1(sK3,sK2) ),
    inference(superposition,[],[f269,f315])).

fof(f315,plain,(
    ! [X1] : k10_relat_1(sK3,X1) = k9_relat_1(k4_relat_1(sK3),X1) ),
    inference(subsumption_resolution,[],[f298,f213])).

fof(f298,plain,(
    ! [X1] :
      ( k10_relat_1(sK3,X1) = k9_relat_1(k4_relat_1(sK3),X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(backward_demodulation,[],[f198,f295])).

fof(f295,plain,(
    k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(resolution,[],[f202,f213])).

fof(f202,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f191,f100])).

fof(f191,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f103,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f198,plain,(
    ! [X1] :
      ( k10_relat_1(sK3,X1) = k9_relat_1(k2_funct_1(sK3),X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f187,f100])).

fof(f187,plain,(
    ! [X1] :
      ( k10_relat_1(sK3,X1) = k9_relat_1(k2_funct_1(sK3),X1)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f103,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f269,plain,(
    k1_relat_1(sK3) = k9_relat_1(k4_relat_1(sK3),sK2) ),
    inference(forward_demodulation,[],[f268,f226])).

fof(f268,plain,(
    k2_relat_1(k4_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),sK2) ),
    inference(forward_demodulation,[],[f267,f229])).

fof(f267,plain,(
    k2_relat_1(k4_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f261,f213])).

fof(f261,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k4_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))) ),
    inference(resolution,[],[f206,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f399,plain,(
    r1_tarski(k10_relat_1(sK3,sK2),sK1) ),
    inference(superposition,[],[f377,f386])).

fof(f386,plain,(
    sK2 = k9_relat_1(sK3,sK1) ),
    inference(superposition,[],[f215,f216])).

fof(f216,plain,(
    sK2 = k7_relset_1(sK1,sK2,sK3,sK1) ),
    inference(forward_demodulation,[],[f208,f104])).

fof(f208,plain,(
    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    inference(resolution,[],[f102,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f215,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK1,sK2,sK3,X0) ),
    inference(resolution,[],[f102,f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f377,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) ),
    inference(resolution,[],[f205,f213])).

fof(f205,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK3)
      | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f194,f100])).

fof(f194,plain,(
    ! [X2] :
      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X2)),X2)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f103,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f366,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | v1_funct_2(k4_relat_1(sK3),sK2,X0)
      | ~ v1_funct_1(k4_relat_1(sK3))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(forward_demodulation,[],[f362,f229])).

fof(f362,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | v1_funct_2(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)),X0)
      | ~ v1_funct_1(k4_relat_1(sK3))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(superposition,[],[f137,f226])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f582,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f455,f312])).

fof(f312,plain,
    ( ~ m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f311,f295])).

fof(f311,plain,
    ( ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f296,f295])).

fof(f296,plain,
    ( ~ m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f105,f295])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f88])).

fof(f455,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f446,f391])).

fof(f391,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f221,f212])).

fof(f212,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f102,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f221,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f211,f101])).

fof(f101,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f211,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f102,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
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
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
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

fof(f233,plain,(
    sK3 = k3_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) ),
    inference(forward_demodulation,[],[f228,f217])).

fof(f228,plain,(
    sK3 = k3_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    inference(resolution,[],[f213,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f100,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f840,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f839,f166])).

fof(f166,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f839,plain,(
    ~ v1_funct_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f838,f682])).

fof(f838,plain,(
    ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f837,f784])).

fof(f784,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f783,f761])).

fof(f761,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f705,f759])).

fof(f759,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f703,f731])).

fof(f731,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f730,f149])).

fof(f149,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f730,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f692,f166])).

fof(f692,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k10_relat_1(k4_relat_1(k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f313,f682])).

fof(f313,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k10_relat_1(k4_relat_1(sK3),X0) ),
    inference(subsumption_resolution,[],[f297,f213])).

fof(f297,plain,(
    ! [X0] :
      ( k9_relat_1(sK3,X0) = k10_relat_1(k4_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(backward_demodulation,[],[f197,f295])).

fof(f197,plain,(
    ! [X0] :
      ( k9_relat_1(sK3,X0) = k10_relat_1(k2_funct_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f186,f100])).

fof(f186,plain,(
    ! [X0] :
      ( k9_relat_1(sK3,X0) = k10_relat_1(k2_funct_1(sK3),X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f103,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f703,plain,(
    ! [X0] : k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f464,f682])).

fof(f464,plain,(
    ! [X0] : k10_relat_1(sK3,k9_relat_1(sK3,X0)) = k3_xboole_0(X0,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f463,f213])).

fof(f463,plain,(
    ! [X0] :
      ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = k3_xboole_0(X0,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f316,f206])).

fof(f316,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(sK3))
      | k10_relat_1(sK3,k9_relat_1(sK3,X0)) = k3_xboole_0(X0,k1_relat_1(sK3)) ) ),
    inference(backward_demodulation,[],[f314,f315])).

fof(f314,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k1_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(backward_demodulation,[],[f278,f313])).

fof(f278,plain,(
    ! [X0] :
      ( k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k1_relat_1(sK3))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(forward_demodulation,[],[f277,f269])).

fof(f277,plain,(
    ! [X0] :
      ( k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK3),sK2))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(forward_demodulation,[],[f276,f229])).

fof(f276,plain,(
    ! [X0] :
      ( k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f273,f213])).

fof(f273,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))))
      | ~ v1_relat_1(k4_relat_1(sK3)) ) ),
    inference(resolution,[],[f207,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f705,plain,(
    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f504,f682])).

fof(f504,plain,(
    k1_relat_1(sK3) = k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f499,f389])).

fof(f499,plain,(
    k10_relat_1(sK3,sK2) = k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(superposition,[],[f464,f230])).

fof(f230,plain,(
    sK2 = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f227,f217])).

fof(f227,plain,(
    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(resolution,[],[f213,f148])).

fof(f783,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f782,f682])).

fof(f782,plain,(
    ! [X0] : v1_funct_2(sK3,k1_relat_1(sK3),X0) ),
    inference(subsumption_resolution,[],[f611,f760])).

fof(f760,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f704,f759])).

fof(f704,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(k1_xboole_0)),X0) ),
    inference(backward_demodulation,[],[f465,f682])).

fof(f465,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK3)),X0) ),
    inference(backward_demodulation,[],[f377,f464])).

fof(f611,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(sK3,k1_relat_1(sK3),X0) ) ),
    inference(backward_demodulation,[],[f239,f596])).

% (26718)Refutation not found, incomplete strategy% (26718)------------------------------
% (26718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26718)Termination reason: Refutation not found, incomplete strategy

% (26718)Memory used [KB]: 1791
% (26718)Time elapsed: 0.111 s
% (26718)------------------------------
% (26718)------------------------------
fof(f239,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | v1_funct_2(sK3,k1_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f238,f213])).

fof(f238,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f234,f100])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f137,f217])).

fof(f837,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f836,f166])).

fof(f836,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f835,f682])).

fof(f835,plain,
    ( ~ v1_funct_2(k4_relat_1(sK3),k1_xboole_0,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f834,f596])).

fof(f834,plain,
    ( ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f833,f719])).

fof(f719,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f676,f682])).

fof(f676,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f598,f171])).

fof(f598,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f102,f596])).

fof(f833,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f832,f166])).

fof(f832,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f831,f682])).

fof(f831,plain,
    ( ~ m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f623,f172])).

fof(f172,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f90])).

fof(f623,plain,
    ( ~ m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k4_relat_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k4_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f312,f596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (26741)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.13/0.52  % (26723)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.52  % (26733)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.13/0.53  % (26732)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.13/0.53  % (26733)Refutation not found, incomplete strategy% (26733)------------------------------
% 1.13/0.53  % (26733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (26731)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.13/0.53  % (26730)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.53  % (26720)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.53  % (26740)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.53  % (26735)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.53  % (26738)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.53  % (26733)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (26733)Memory used [KB]: 10746
% 1.23/0.53  % (26733)Time elapsed: 0.102 s
% 1.23/0.53  % (26733)------------------------------
% 1.23/0.53  % (26733)------------------------------
% 1.23/0.53  % (26746)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.54  % (26745)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.54  % (26742)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.23/0.54  % (26731)Refutation found. Thanks to Tanya!
% 1.23/0.54  % SZS status Theorem for theBenchmark
% 1.23/0.54  % (26727)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.54  % (26736)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.23/0.54  % (26729)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.54  % (26719)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.55  % (26724)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.55  % (26726)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.55  % (26717)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.55  % (26739)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.55  % (26725)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.55  % (26744)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.55  % (26728)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.55  % (26721)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.23/0.55  % (26743)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.23/0.55  % (26718)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.56  % (26737)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.56  % SZS output start Proof for theBenchmark
% 1.23/0.56  fof(f841,plain,(
% 1.23/0.56    $false),
% 1.23/0.56    inference(subsumption_resolution,[],[f840,f683])).
% 1.23/0.56  fof(f683,plain,(
% 1.23/0.56    v1_funct_1(k1_xboole_0)),
% 1.23/0.56    inference(backward_demodulation,[],[f100,f682])).
% 1.23/0.56  fof(f682,plain,(
% 1.23/0.56    k1_xboole_0 = sK3),
% 1.23/0.56    inference(forward_demodulation,[],[f681,f167])).
% 1.23/0.56  fof(f167,plain,(
% 1.23/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f3])).
% 1.23/0.56  fof(f3,axiom,(
% 1.23/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.23/0.56  fof(f681,plain,(
% 1.23/0.56    sK3 = k3_xboole_0(sK3,k1_xboole_0)),
% 1.23/0.56    inference(forward_demodulation,[],[f610,f171])).
% 1.23/0.56  fof(f171,plain,(
% 1.23/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.23/0.56    inference(equality_resolution,[],[f117])).
% 1.23/0.56  fof(f117,plain,(
% 1.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.23/0.56    inference(cnf_transformation,[],[f90])).
% 1.23/0.56  fof(f90,plain,(
% 1.23/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.23/0.56    inference(flattening,[],[f89])).
% 1.23/0.56  fof(f89,plain,(
% 1.23/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.23/0.56    inference(nnf_transformation,[],[f10])).
% 1.23/0.56  fof(f10,axiom,(
% 1.23/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.23/0.56  fof(f610,plain,(
% 1.23/0.56    sK3 = k3_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))),
% 1.23/0.56    inference(backward_demodulation,[],[f233,f596])).
% 1.23/0.56  fof(f596,plain,(
% 1.23/0.56    k1_xboole_0 = sK2),
% 1.23/0.56    inference(subsumption_resolution,[],[f595,f213])).
% 1.23/0.56  fof(f213,plain,(
% 1.23/0.56    v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f102,f135])).
% 1.23/0.56  fof(f135,plain,(
% 1.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f72])).
% 1.23/0.56  fof(f72,plain,(
% 1.23/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(ennf_transformation,[],[f34])).
% 1.23/0.56  fof(f34,axiom,(
% 1.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.23/0.56  fof(f102,plain,(
% 1.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.23/0.56    inference(cnf_transformation,[],[f88])).
% 1.23/0.56  fof(f88,plain,(
% 1.23/0.56    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.23/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f87])).
% 1.23/0.56  % (26734)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.23/0.56  fof(f87,plain,(
% 1.23/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.23/0.56    introduced(choice_axiom,[])).
% 1.23/0.56  fof(f47,plain,(
% 1.23/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.23/0.56    inference(flattening,[],[f46])).
% 1.23/0.56  fof(f46,plain,(
% 1.23/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.23/0.56    inference(ennf_transformation,[],[f45])).
% 1.23/0.56  fof(f45,negated_conjecture,(
% 1.23/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.23/0.56    inference(negated_conjecture,[],[f44])).
% 1.23/0.56  fof(f44,conjecture,(
% 1.23/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.23/0.56  fof(f595,plain,(
% 1.23/0.56    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f591,f207])).
% 1.23/0.56  fof(f207,plain,(
% 1.23/0.56    v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(subsumption_resolution,[],[f196,f100])).
% 1.23/0.56  fof(f196,plain,(
% 1.23/0.56    v1_funct_1(k4_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f103,f127])).
% 1.23/0.56  fof(f127,plain,(
% 1.23/0.56    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f68])).
% 1.23/0.56  fof(f68,plain,(
% 1.23/0.56    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.56    inference(flattening,[],[f67])).
% 1.23/0.56  fof(f67,plain,(
% 1.23/0.56    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.23/0.56    inference(ennf_transformation,[],[f26])).
% 1.23/0.56  fof(f26,axiom,(
% 1.23/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).
% 1.23/0.56  fof(f103,plain,(
% 1.23/0.56    v2_funct_1(sK3)),
% 1.23/0.56    inference(cnf_transformation,[],[f88])).
% 1.23/0.56  fof(f591,plain,(
% 1.23/0.56    ~v1_funct_1(k4_relat_1(sK3)) | k1_xboole_0 = sK2),
% 1.23/0.56    inference(subsumption_resolution,[],[f582,f556])).
% 1.23/0.56  fof(f556,plain,(
% 1.23/0.56    v1_funct_2(k4_relat_1(sK3),sK2,sK1)),
% 1.23/0.56    inference(subsumption_resolution,[],[f555,f213])).
% 1.23/0.56  fof(f555,plain,(
% 1.23/0.56    v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f553,f207])).
% 1.23/0.56  fof(f553,plain,(
% 1.23/0.56    ~v1_funct_1(k4_relat_1(sK3)) | v1_funct_2(k4_relat_1(sK3),sK2,sK1)),
% 1.23/0.56    inference(subsumption_resolution,[],[f550,f452])).
% 1.23/0.56  fof(f452,plain,(
% 1.23/0.56    v1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(resolution,[],[f446,f135])).
% 1.23/0.56  fof(f446,plain,(
% 1.23/0.56    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 1.23/0.56    inference(subsumption_resolution,[],[f445,f213])).
% 1.23/0.56  fof(f445,plain,(
% 1.23/0.56    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f284,f206])).
% 1.23/0.56  fof(f206,plain,(
% 1.23/0.56    v1_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(subsumption_resolution,[],[f195,f100])).
% 1.23/0.56  fof(f195,plain,(
% 1.23/0.56    v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f103,f126])).
% 1.23/0.56  fof(f126,plain,(
% 1.23/0.56    ( ! [X0] : (~v2_funct_1(X0) | v1_relat_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f68])).
% 1.23/0.56  fof(f284,plain,(
% 1.23/0.56    ~v1_relat_1(k4_relat_1(sK3)) | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 1.23/0.56    inference(forward_demodulation,[],[f283,f229])).
% 1.23/0.56  fof(f229,plain,(
% 1.23/0.56    sK2 = k1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f225,f217])).
% 1.23/0.56  fof(f217,plain,(
% 1.23/0.56    sK2 = k2_relat_1(sK3)),
% 1.23/0.56    inference(forward_demodulation,[],[f210,f104])).
% 1.23/0.56  fof(f104,plain,(
% 1.23/0.56    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.23/0.56    inference(cnf_transformation,[],[f88])).
% 1.23/0.56  fof(f210,plain,(
% 1.23/0.56    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f102,f124])).
% 1.23/0.56  fof(f124,plain,(
% 1.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f64])).
% 1.23/0.56  fof(f64,plain,(
% 1.23/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(ennf_transformation,[],[f36])).
% 1.23/0.56  fof(f36,axiom,(
% 1.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.23/0.56  fof(f225,plain,(
% 1.23/0.56    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(resolution,[],[f213,f150])).
% 1.23/0.56  fof(f150,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.23/0.56    inference(cnf_transformation,[],[f84])).
% 1.23/0.56  fof(f84,plain,(
% 1.23/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.23/0.56    inference(ennf_transformation,[],[f21])).
% 1.23/0.56  fof(f21,axiom,(
% 1.23/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.23/0.56  fof(f283,plain,(
% 1.23/0.56    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) | ~v1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f282,f226])).
% 1.23/0.56  % (26722)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.56  fof(f226,plain,(
% 1.23/0.56    k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(resolution,[],[f213,f151])).
% 1.23/0.56  fof(f151,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.23/0.56    inference(cnf_transformation,[],[f84])).
% 1.23/0.56  fof(f282,plain,(
% 1.23/0.56    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k2_relat_1(k4_relat_1(sK3))))) | ~v1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(subsumption_resolution,[],[f275,f213])).
% 1.23/0.56  fof(f275,plain,(
% 1.23/0.56    ~v1_relat_1(sK3) | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k2_relat_1(k4_relat_1(sK3))))) | ~v1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(resolution,[],[f207,f141])).
% 1.23/0.56  fof(f141,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f76])).
% 1.23/0.56  fof(f76,plain,(
% 1.23/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.56    inference(flattening,[],[f75])).
% 1.23/0.56  fof(f75,plain,(
% 1.23/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.23/0.56    inference(ennf_transformation,[],[f42])).
% 1.23/0.56  fof(f42,axiom,(
% 1.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.23/0.56  fof(f550,plain,(
% 1.23/0.56    v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(resolution,[],[f366,f402])).
% 1.23/0.56  fof(f402,plain,(
% 1.23/0.56    r1_tarski(k1_relat_1(sK3),sK1)),
% 1.23/0.56    inference(forward_demodulation,[],[f399,f389])).
% 1.23/0.56  fof(f389,plain,(
% 1.23/0.56    k1_relat_1(sK3) = k10_relat_1(sK3,sK2)),
% 1.23/0.56    inference(superposition,[],[f269,f315])).
% 1.23/0.56  fof(f315,plain,(
% 1.23/0.56    ( ! [X1] : (k10_relat_1(sK3,X1) = k9_relat_1(k4_relat_1(sK3),X1)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f298,f213])).
% 1.23/0.56  fof(f298,plain,(
% 1.23/0.56    ( ! [X1] : (k10_relat_1(sK3,X1) = k9_relat_1(k4_relat_1(sK3),X1) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(backward_demodulation,[],[f198,f295])).
% 1.23/0.56  fof(f295,plain,(
% 1.23/0.56    k2_funct_1(sK3) = k4_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f202,f213])).
% 1.23/0.56  fof(f202,plain,(
% 1.23/0.56    ~v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3)),
% 1.23/0.56    inference(subsumption_resolution,[],[f191,f100])).
% 1.23/0.56  fof(f191,plain,(
% 1.23/0.56    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f103,f111])).
% 1.23/0.56  fof(f111,plain,(
% 1.23/0.56    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f57])).
% 1.23/0.56  fof(f57,plain,(
% 1.23/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.56    inference(flattening,[],[f56])).
% 1.23/0.56  fof(f56,plain,(
% 1.23/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.23/0.56    inference(ennf_transformation,[],[f25])).
% 1.23/0.56  fof(f25,axiom,(
% 1.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.23/0.56  fof(f198,plain,(
% 1.23/0.56    ( ! [X1] : (k10_relat_1(sK3,X1) = k9_relat_1(k2_funct_1(sK3),X1) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f187,f100])).
% 1.23/0.56  fof(f187,plain,(
% 1.23/0.56    ( ! [X1] : (k10_relat_1(sK3,X1) = k9_relat_1(k2_funct_1(sK3),X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(resolution,[],[f103,f107])).
% 1.23/0.56  fof(f107,plain,(
% 1.23/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f51])).
% 1.23/0.56  fof(f51,plain,(
% 1.23/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.56    inference(flattening,[],[f50])).
% 1.23/0.56  fof(f50,plain,(
% 1.23/0.56    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.56    inference(ennf_transformation,[],[f31])).
% 1.23/0.56  fof(f31,axiom,(
% 1.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 1.23/0.56  fof(f269,plain,(
% 1.23/0.56    k1_relat_1(sK3) = k9_relat_1(k4_relat_1(sK3),sK2)),
% 1.23/0.56    inference(forward_demodulation,[],[f268,f226])).
% 1.23/0.56  fof(f268,plain,(
% 1.23/0.56    k2_relat_1(k4_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),sK2)),
% 1.23/0.56    inference(forward_demodulation,[],[f267,f229])).
% 1.23/0.56  fof(f267,plain,(
% 1.23/0.56    k2_relat_1(k4_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))),
% 1.23/0.56    inference(subsumption_resolution,[],[f261,f213])).
% 1.23/0.56  fof(f261,plain,(
% 1.23/0.56    ~v1_relat_1(sK3) | k2_relat_1(k4_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))),
% 1.23/0.56    inference(resolution,[],[f206,f148])).
% 1.23/0.56  fof(f148,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f83])).
% 1.23/0.56  fof(f83,plain,(
% 1.23/0.56    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.56    inference(ennf_transformation,[],[f17])).
% 1.23/0.56  fof(f17,axiom,(
% 1.23/0.56    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.23/0.56  fof(f399,plain,(
% 1.23/0.56    r1_tarski(k10_relat_1(sK3,sK2),sK1)),
% 1.23/0.56    inference(superposition,[],[f377,f386])).
% 1.23/0.56  fof(f386,plain,(
% 1.23/0.56    sK2 = k9_relat_1(sK3,sK1)),
% 1.23/0.56    inference(superposition,[],[f215,f216])).
% 1.23/0.56  fof(f216,plain,(
% 1.23/0.56    sK2 = k7_relset_1(sK1,sK2,sK3,sK1)),
% 1.23/0.56    inference(forward_demodulation,[],[f208,f104])).
% 1.23/0.56  fof(f208,plain,(
% 1.23/0.56    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 1.23/0.56    inference(resolution,[],[f102,f122])).
% 1.23/0.56  fof(f122,plain,(
% 1.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f63])).
% 1.23/0.56  fof(f63,plain,(
% 1.23/0.56    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(ennf_transformation,[],[f38])).
% 1.23/0.56  fof(f38,axiom,(
% 1.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.23/0.56  fof(f215,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK1,sK2,sK3,X0)) )),
% 1.23/0.56    inference(resolution,[],[f102,f147])).
% 1.23/0.56  fof(f147,plain,(
% 1.23/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f82])).
% 1.23/0.56  fof(f82,plain,(
% 1.23/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(ennf_transformation,[],[f37])).
% 1.23/0.56  fof(f37,axiom,(
% 1.23/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.23/0.56  fof(f377,plain,(
% 1.23/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0)) )),
% 1.23/0.56    inference(resolution,[],[f205,f213])).
% 1.23/0.56  fof(f205,plain,(
% 1.23/0.56    ( ! [X2] : (~v1_relat_1(sK3) | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X2)),X2)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f194,f100])).
% 1.23/0.56  fof(f194,plain,(
% 1.23/0.56    ( ! [X2] : (r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X2)),X2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(resolution,[],[f103,f125])).
% 1.23/0.56  fof(f125,plain,(
% 1.23/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f66])).
% 1.23/0.56  fof(f66,plain,(
% 1.23/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.56    inference(flattening,[],[f65])).
% 1.23/0.56  fof(f65,plain,(
% 1.23/0.56    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.56    inference(ennf_transformation,[],[f29])).
% 1.23/0.56  fof(f29,axiom,(
% 1.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.23/0.56  fof(f366,plain,(
% 1.23/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | v1_funct_2(k4_relat_1(sK3),sK2,X0) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(forward_demodulation,[],[f362,f229])).
% 1.23/0.56  fof(f362,plain,(
% 1.23/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | v1_funct_2(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)),X0) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(superposition,[],[f137,f226])).
% 1.23/0.56  fof(f137,plain,(
% 1.23/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f74])).
% 1.23/0.56  fof(f74,plain,(
% 1.23/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.56    inference(flattening,[],[f73])).
% 1.23/0.56  fof(f73,plain,(
% 1.23/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.56    inference(ennf_transformation,[],[f43])).
% 1.23/0.56  fof(f43,axiom,(
% 1.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.23/0.56  fof(f582,plain,(
% 1.23/0.56    k1_xboole_0 = sK2 | ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(resolution,[],[f455,f312])).
% 1.23/0.56  fof(f312,plain,(
% 1.23/0.56    ~m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f311,f295])).
% 1.23/0.56  fof(f311,plain,(
% 1.23/0.56    ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f296,f295])).
% 1.23/0.56  fof(f296,plain,(
% 1.23/0.56    ~m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.23/0.56    inference(backward_demodulation,[],[f105,f295])).
% 1.23/0.56  fof(f105,plain,(
% 1.23/0.56    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.23/0.56    inference(cnf_transformation,[],[f88])).
% 1.23/0.56  fof(f455,plain,(
% 1.23/0.56    m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k1_xboole_0 = sK2),
% 1.23/0.56    inference(superposition,[],[f446,f391])).
% 1.23/0.56  fof(f391,plain,(
% 1.23/0.56    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.23/0.56    inference(superposition,[],[f221,f212])).
% 1.23/0.56  fof(f212,plain,(
% 1.23/0.56    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.23/0.56    inference(resolution,[],[f102,f134])).
% 1.23/0.56  fof(f134,plain,(
% 1.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f71])).
% 1.23/0.56  fof(f71,plain,(
% 1.23/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(ennf_transformation,[],[f35])).
% 1.23/0.56  fof(f35,axiom,(
% 1.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.23/0.56  fof(f221,plain,(
% 1.23/0.56    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.23/0.56    inference(subsumption_resolution,[],[f211,f101])).
% 1.23/0.56  fof(f101,plain,(
% 1.23/0.56    v1_funct_2(sK3,sK1,sK2)),
% 1.23/0.56    inference(cnf_transformation,[],[f88])).
% 1.23/0.56  fof(f211,plain,(
% 1.23/0.56    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.23/0.56    inference(resolution,[],[f102,f128])).
% 1.23/0.56  fof(f128,plain,(
% 1.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.23/0.56    inference(cnf_transformation,[],[f92])).
% 1.23/0.56  fof(f92,plain,(
% 1.23/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(nnf_transformation,[],[f70])).
% 1.23/0.56  fof(f70,plain,(
% 1.23/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(flattening,[],[f69])).
% 1.23/0.56  fof(f69,plain,(
% 1.23/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.56    inference(ennf_transformation,[],[f39])).
% 1.23/0.56  fof(f39,axiom,(
% 1.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.23/0.56  fof(f233,plain,(
% 1.23/0.56    sK3 = k3_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2))),
% 1.23/0.56    inference(forward_demodulation,[],[f228,f217])).
% 1.23/0.56  fof(f228,plain,(
% 1.23/0.56    sK3 = k3_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 1.23/0.56    inference(resolution,[],[f213,f143])).
% 1.23/0.56  fof(f143,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.23/0.56    inference(cnf_transformation,[],[f77])).
% 1.23/0.56  fof(f77,plain,(
% 1.23/0.56    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.23/0.56    inference(ennf_transformation,[],[f19])).
% 1.23/0.56  fof(f19,axiom,(
% 1.23/0.56    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.23/0.56  fof(f100,plain,(
% 1.23/0.56    v1_funct_1(sK3)),
% 1.23/0.56    inference(cnf_transformation,[],[f88])).
% 1.23/0.56  fof(f840,plain,(
% 1.23/0.56    ~v1_funct_1(k1_xboole_0)),
% 1.23/0.56    inference(forward_demodulation,[],[f839,f166])).
% 1.23/0.56  fof(f166,plain,(
% 1.23/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.23/0.56    inference(cnf_transformation,[],[f24])).
% 1.23/0.56  fof(f24,axiom,(
% 1.23/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 1.23/0.56  fof(f839,plain,(
% 1.23/0.56    ~v1_funct_1(k4_relat_1(k1_xboole_0))),
% 1.23/0.56    inference(forward_demodulation,[],[f838,f682])).
% 1.23/0.56  fof(f838,plain,(
% 1.23/0.56    ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(subsumption_resolution,[],[f837,f784])).
% 1.23/0.56  fof(f784,plain,(
% 1.23/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.23/0.56    inference(forward_demodulation,[],[f783,f761])).
% 1.23/0.56  fof(f761,plain,(
% 1.23/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.56    inference(forward_demodulation,[],[f705,f759])).
% 1.23/0.56  fof(f759,plain,(
% 1.23/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_relat_1(k1_xboole_0))) )),
% 1.23/0.56    inference(forward_demodulation,[],[f703,f731])).
% 1.23/0.56  fof(f731,plain,(
% 1.23/0.56    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.23/0.56    inference(forward_demodulation,[],[f730,f149])).
% 1.23/0.56  fof(f149,plain,(
% 1.23/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f18])).
% 1.23/0.56  fof(f18,axiom,(
% 1.23/0.56    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 1.23/0.56  fof(f730,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,X0)) )),
% 1.23/0.56    inference(forward_demodulation,[],[f692,f166])).
% 1.23/0.56  fof(f692,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k10_relat_1(k4_relat_1(k1_xboole_0),X0)) )),
% 1.23/0.56    inference(backward_demodulation,[],[f313,f682])).
% 1.23/0.56  fof(f313,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(sK3,X0) = k10_relat_1(k4_relat_1(sK3),X0)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f297,f213])).
% 1.23/0.56  fof(f297,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(sK3,X0) = k10_relat_1(k4_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(backward_demodulation,[],[f197,f295])).
% 1.23/0.56  fof(f197,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(sK3,X0) = k10_relat_1(k2_funct_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f186,f100])).
% 1.23/0.56  fof(f186,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(sK3,X0) = k10_relat_1(k2_funct_1(sK3),X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(resolution,[],[f103,f106])).
% 1.23/0.56  fof(f106,plain,(
% 1.23/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f49])).
% 1.23/0.56  fof(f49,plain,(
% 1.23/0.56    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.56    inference(flattening,[],[f48])).
% 1.23/0.56  fof(f48,plain,(
% 1.23/0.56    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.56    inference(ennf_transformation,[],[f30])).
% 1.23/0.56  fof(f30,axiom,(
% 1.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 1.23/0.56  fof(f703,plain,(
% 1.23/0.56    ( ! [X0] : (k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_relat_1(k1_xboole_0))) )),
% 1.23/0.56    inference(backward_demodulation,[],[f464,f682])).
% 1.23/0.56  fof(f464,plain,(
% 1.23/0.56    ( ! [X0] : (k10_relat_1(sK3,k9_relat_1(sK3,X0)) = k3_xboole_0(X0,k1_relat_1(sK3))) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f463,f213])).
% 1.23/0.56  fof(f463,plain,(
% 1.23/0.56    ( ! [X0] : (k10_relat_1(sK3,k9_relat_1(sK3,X0)) = k3_xboole_0(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(resolution,[],[f316,f206])).
% 1.23/0.56  fof(f316,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_relat_1(k4_relat_1(sK3)) | k10_relat_1(sK3,k9_relat_1(sK3,X0)) = k3_xboole_0(X0,k1_relat_1(sK3))) )),
% 1.23/0.56    inference(backward_demodulation,[],[f314,f315])).
% 1.23/0.56  fof(f314,plain,(
% 1.23/0.56    ( ! [X0] : (k3_xboole_0(X0,k1_relat_1(sK3)) = k9_relat_1(k4_relat_1(sK3),k9_relat_1(sK3,X0)) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(backward_demodulation,[],[f278,f313])).
% 1.23/0.56  fof(f278,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k1_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(forward_demodulation,[],[f277,f269])).
% 1.23/0.56  fof(f277,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK3),sK2)) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(forward_demodulation,[],[f276,f229])).
% 1.23/0.56  fof(f276,plain,(
% 1.23/0.56    ( ! [X0] : (k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f273,f213])).
% 1.23/0.56  fof(f273,plain,(
% 1.23/0.56    ( ! [X0] : (~v1_relat_1(sK3) | k9_relat_1(k4_relat_1(sK3),k10_relat_1(k4_relat_1(sK3),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))) | ~v1_relat_1(k4_relat_1(sK3))) )),
% 1.23/0.56    inference(resolution,[],[f207,f146])).
% 1.23/0.56  fof(f146,plain,(
% 1.23/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.23/0.56    inference(cnf_transformation,[],[f81])).
% 1.23/0.56  fof(f81,plain,(
% 1.23/0.56    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.56    inference(flattening,[],[f80])).
% 1.23/0.56  fof(f80,plain,(
% 1.23/0.56    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.56    inference(ennf_transformation,[],[f28])).
% 1.23/0.56  fof(f28,axiom,(
% 1.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.23/0.56  fof(f705,plain,(
% 1.23/0.56    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 1.23/0.56    inference(backward_demodulation,[],[f504,f682])).
% 1.23/0.56  fof(f504,plain,(
% 1.23/0.56    k1_relat_1(sK3) = k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f499,f389])).
% 1.23/0.56  fof(f499,plain,(
% 1.23/0.56    k10_relat_1(sK3,sK2) = k3_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3))),
% 1.23/0.56    inference(superposition,[],[f464,f230])).
% 1.23/0.56  fof(f230,plain,(
% 1.23/0.56    sK2 = k9_relat_1(sK3,k1_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f227,f217])).
% 1.23/0.56  fof(f227,plain,(
% 1.23/0.56    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)),
% 1.23/0.56    inference(resolution,[],[f213,f148])).
% 1.23/0.56  fof(f783,plain,(
% 1.23/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) )),
% 1.23/0.56    inference(forward_demodulation,[],[f782,f682])).
% 1.23/0.56  fof(f782,plain,(
% 1.23/0.56    ( ! [X0] : (v1_funct_2(sK3,k1_relat_1(sK3),X0)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f611,f760])).
% 1.23/0.56  fof(f760,plain,(
% 1.23/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.56    inference(forward_demodulation,[],[f704,f759])).
% 1.23/0.56  fof(f704,plain,(
% 1.23/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(k1_xboole_0)),X0)) )),
% 1.23/0.56    inference(backward_demodulation,[],[f465,f682])).
% 1.23/0.56  fof(f465,plain,(
% 1.23/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK3)),X0)) )),
% 1.23/0.56    inference(backward_demodulation,[],[f377,f464])).
% 1.23/0.56  fof(f611,plain,(
% 1.23/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0)) )),
% 1.23/0.56    inference(backward_demodulation,[],[f239,f596])).
% 1.23/0.56  % (26718)Refutation not found, incomplete strategy% (26718)------------------------------
% 1.23/0.56  % (26718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.56  % (26718)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.56  
% 1.23/0.56  % (26718)Memory used [KB]: 1791
% 1.23/0.56  % (26718)Time elapsed: 0.111 s
% 1.23/0.56  % (26718)------------------------------
% 1.23/0.56  % (26718)------------------------------
% 1.23/0.56  fof(f239,plain,(
% 1.23/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f238,f213])).
% 1.23/0.56  fof(f238,plain,(
% 1.23/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(subsumption_resolution,[],[f234,f100])).
% 1.23/0.56  fof(f234,plain,(
% 1.23/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.23/0.56    inference(superposition,[],[f137,f217])).
% 1.23/0.56  fof(f837,plain,(
% 1.23/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f836,f166])).
% 1.23/0.56  fof(f836,plain,(
% 1.23/0.56    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f835,f682])).
% 1.23/0.56  fof(f835,plain,(
% 1.23/0.56    ~v1_funct_2(k4_relat_1(sK3),k1_xboole_0,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f834,f596])).
% 1.23/0.56  fof(f834,plain,(
% 1.23/0.56    ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(subsumption_resolution,[],[f833,f719])).
% 1.23/0.56  fof(f719,plain,(
% 1.23/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.23/0.56    inference(backward_demodulation,[],[f676,f682])).
% 1.23/0.56  fof(f676,plain,(
% 1.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.23/0.56    inference(forward_demodulation,[],[f598,f171])).
% 1.23/0.56  fof(f598,plain,(
% 1.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.23/0.56    inference(backward_demodulation,[],[f102,f596])).
% 1.23/0.56  fof(f833,plain,(
% 1.23/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f832,f166])).
% 1.23/0.56  fof(f832,plain,(
% 1.23/0.56    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f831,f682])).
% 1.23/0.56  fof(f831,plain,(
% 1.23/0.56    ~m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(forward_demodulation,[],[f623,f172])).
% 1.23/0.56  fof(f172,plain,(
% 1.23/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.23/0.56    inference(equality_resolution,[],[f116])).
% 1.23/0.56  fof(f116,plain,(
% 1.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.23/0.56    inference(cnf_transformation,[],[f90])).
% 1.23/0.56  fof(f623,plain,(
% 1.23/0.56    ~m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k4_relat_1(sK3),sK2,sK1) | ~v1_funct_1(k4_relat_1(sK3))),
% 1.23/0.56    inference(backward_demodulation,[],[f312,f596])).
% 1.23/0.56  % SZS output end Proof for theBenchmark
% 1.23/0.56  % (26731)------------------------------
% 1.23/0.56  % (26731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.56  % (26731)Termination reason: Refutation
% 1.23/0.56  
% 1.23/0.56  % (26731)Memory used [KB]: 2046
% 1.23/0.56  % (26731)Time elapsed: 0.129 s
% 1.23/0.56  % (26731)------------------------------
% 1.23/0.56  % (26731)------------------------------
% 1.23/0.57  % (26716)Success in time 0.188 s
%------------------------------------------------------------------------------
