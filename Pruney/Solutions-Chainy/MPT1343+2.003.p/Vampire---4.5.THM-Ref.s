%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:36 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  215 (8061 expanded)
%              Number of leaves         :   34 (3216 expanded)
%              Depth                    :   28
%              Number of atoms          :  599 (60078 expanded)
%              Number of equality atoms :  184 (16118 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1168,f512])).

fof(f512,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k8_relset_1(X4,X5,k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f508,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f508,plain,(
    ! [X6,X4,X5] : k8_relset_1(X4,X5,k1_xboole_0,X6) = k10_relat_1(k1_xboole_0,X6) ),
    inference(resolution,[],[f147,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f1168,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f944,f319])).

fof(f319,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f311,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f311,plain,(
    v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f308,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f308,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f306,f171])).

fof(f171,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f133,f103])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f306,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f303,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f303,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f302,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

% (5719)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (5727)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (5711)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f86,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f302,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f301,f102])).

fof(f102,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f301,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f300,f106])).

fof(f106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f300,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f127,f104])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f944,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k4_relat_1(k1_xboole_0),sK3) ),
    inference(backward_demodulation,[],[f863,f869])).

fof(f869,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f840,f109])).

fof(f840,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f830,f314])).

fof(f314,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f304,f125])).

fof(f304,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f302,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f830,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f805,f152])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f805,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f385,f789])).

fof(f789,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f788,f556])).

fof(f556,plain,(
    ! [X5] : k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X5) = k9_relat_1(sK2,X5) ),
    inference(forward_demodulation,[],[f551,f447])).

fof(f447,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k4_relat_1(sK2),X0) ),
    inference(forward_demodulation,[],[f446,f249])).

fof(f249,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f248,f184])).

fof(f184,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f176,f169])).

fof(f169,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f163,f161])).

fof(f161,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f108,f93])).

fof(f93,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f82,f81,f80,f79])).

fof(f79,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
    ( ? [X3] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f38,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f163,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f96,f160])).

fof(f160,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f108,f92])).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

fof(f176,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f114,f120])).

fof(f120,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f248,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f247,f94])).

fof(f94,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f247,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f117,f99])).

fof(f99,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f446,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f445,f184])).

fof(f445,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f444,f94])).

fof(f444,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f129,f99])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f551,plain,(
    ! [X5] : k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X5) = k10_relat_1(k4_relat_1(sK2),X5) ),
    inference(resolution,[],[f507,f291])).

fof(f291,plain,(
    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f282,f290])).

fof(f290,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f289,f249])).

fof(f289,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f288,f184])).

fof(f288,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f287,f94])).

fof(f287,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f119,f99])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f282,plain,(
    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f280,f255])).

fof(f255,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f254,f184])).

fof(f254,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f94])).

fof(f251,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f115,f249])).

fof(f115,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f280,plain,
    ( r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[],[f113,f275])).

fof(f275,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f274,f249])).

fof(f274,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f273,f184])).

fof(f273,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f272,f94])).

fof(f272,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f118,f99])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f507,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(resolution,[],[f147,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f788,plain,
    ( k9_relat_1(sK2,sK3) != k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),sK3)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f784,f660])).

fof(f660,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f659,f184])).

fof(f659,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f658,f206])).

fof(f206,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f140,f169])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f658,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f657,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f657,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f656,f94])).

fof(f656,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f655,f383])).

fof(f383,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f169,f380])).

fof(f380,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f168,f376])).

fof(f376,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f139,f169])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f168,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f165,f161])).

fof(f165,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f98,f160])).

fof(f98,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f655,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f155,f384])).

fof(f384,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f170,f380])).

fof(f170,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f162,f161])).

fof(f162,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f95,f160])).

fof(f95,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f784,plain,(
    k9_relat_1(sK2,sK3) != k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2),sK3) ),
    inference(backward_demodulation,[],[f506,f783])).

fof(f783,plain,(
    k4_relat_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f782,f383])).

fof(f782,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | k4_relat_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f780,f388])).

fof(f388,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f376,f380])).

fof(f780,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | k4_relat_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f719,f384])).

fof(f719,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2) ) ),
    inference(forward_demodulation,[],[f718,f249])).

fof(f718,plain,(
    ! [X0,X1] :
      ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f717,f94])).

fof(f717,plain,(
    ! [X0,X1] :
      ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f141,f99])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f506,plain,(
    k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),sK3) != k9_relat_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f382,f502])).

fof(f502,plain,(
    ! [X7] : k7_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X7) = k9_relat_1(sK2,X7) ),
    inference(resolution,[],[f146,f383])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f382,plain,(
    k7_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK3) != k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),sK3) ),
    inference(backward_demodulation,[],[f167,f380])).

fof(f167,plain,(
    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    inference(backward_demodulation,[],[f166,f161])).

fof(f166,plain,(
    k7_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(backward_demodulation,[],[f100,f160])).

fof(f100,plain,(
    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f385,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f174,f380])).

fof(f174,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(resolution,[],[f169,f133])).

fof(f863,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k4_relat_1(sK2),sK3) ),
    inference(backward_demodulation,[],[f825,f856])).

fof(f856,plain,(
    ! [X8] : k1_xboole_0 = k9_relat_1(sK2,X8) ),
    inference(forward_demodulation,[],[f851,f789])).

fof(f851,plain,(
    ! [X8] : k2_relat_1(sK2) = k9_relat_1(sK2,X8) ),
    inference(backward_demodulation,[],[f221,f839])).

fof(f839,plain,(
    ! [X0] : sK2 = k7_relat_1(sK2,X0) ),
    inference(resolution,[],[f830,f236])).

fof(f236,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k7_relat_1(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f226,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f175,f134])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f114,f106])).

fof(f226,plain,(
    ! [X2,X1] :
      ( k7_relat_1(X1,X2) = X1
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f130,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f207,f134])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f140,f152])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f221,plain,(
    ! [X8] : k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8) ),
    inference(resolution,[],[f126,f184])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f825,plain,(
    k9_relat_1(sK2,sK3) != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k4_relat_1(sK2),sK3) ),
    inference(backward_demodulation,[],[f784,f789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:40:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (5707)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (5715)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (5705)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (5714)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (5723)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (5721)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (5722)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (5706)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (5713)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.56  % (5706)Refutation not found, incomplete strategy% (5706)------------------------------
% 1.44/0.56  % (5706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (5715)Refutation not found, incomplete strategy% (5715)------------------------------
% 1.44/0.57  % (5715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (5715)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (5715)Memory used [KB]: 10746
% 1.44/0.57  % (5715)Time elapsed: 0.140 s
% 1.44/0.57  % (5715)------------------------------
% 1.44/0.57  % (5715)------------------------------
% 1.44/0.58  % (5706)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (5706)Memory used [KB]: 10874
% 1.44/0.58  % (5706)Time elapsed: 0.131 s
% 1.44/0.58  % (5706)------------------------------
% 1.44/0.58  % (5706)------------------------------
% 1.44/0.58  % (5700)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.60  % (5716)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.60  % (5712)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.61  % (5718)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.61  % (5699)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.61  % (5710)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.61  % (5702)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.56/0.62  % (5724)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.62  % (5704)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.62  % (5701)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.62  % (5708)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.62  % (5720)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.62  % (5726)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.62  % (5708)Refutation not found, incomplete strategy% (5708)------------------------------
% 1.56/0.62  % (5708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (5708)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (5708)Memory used [KB]: 10746
% 1.56/0.62  % (5708)Time elapsed: 0.191 s
% 1.56/0.62  % (5708)------------------------------
% 1.56/0.62  % (5708)------------------------------
% 1.56/0.63  % (5717)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.63  % (5698)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.63  % (5709)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.64  % (5709)Refutation not found, incomplete strategy% (5709)------------------------------
% 1.56/0.64  % (5709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.64  % (5709)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.64  
% 1.56/0.64  % (5709)Memory used [KB]: 10746
% 1.56/0.64  % (5709)Time elapsed: 0.199 s
% 1.56/0.64  % (5709)------------------------------
% 1.56/0.64  % (5709)------------------------------
% 1.56/0.64  % (5725)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.56/0.64  % (5703)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.64  % (5705)Refutation found. Thanks to Tanya!
% 1.56/0.64  % SZS status Theorem for theBenchmark
% 1.56/0.64  % SZS output start Proof for theBenchmark
% 1.56/0.64  fof(f1169,plain,(
% 1.56/0.64    $false),
% 1.56/0.64    inference(subsumption_resolution,[],[f1168,f512])).
% 1.56/0.64  fof(f512,plain,(
% 1.56/0.64    ( ! [X6,X4,X5] : (k1_xboole_0 = k8_relset_1(X4,X5,k1_xboole_0,X6)) )),
% 1.56/0.64    inference(forward_demodulation,[],[f508,f104])).
% 1.56/0.64  fof(f104,plain,(
% 1.56/0.64    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.56/0.64    inference(cnf_transformation,[],[f20])).
% 1.56/0.64  fof(f20,axiom,(
% 1.56/0.64    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.56/0.64  fof(f508,plain,(
% 1.56/0.64    ( ! [X6,X4,X5] : (k8_relset_1(X4,X5,k1_xboole_0,X6) = k10_relat_1(k1_xboole_0,X6)) )),
% 1.56/0.64    inference(resolution,[],[f147,f103])).
% 1.56/0.64  fof(f103,plain,(
% 1.56/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.56/0.64    inference(cnf_transformation,[],[f12])).
% 1.56/0.64  fof(f12,axiom,(
% 1.56/0.64    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.56/0.64  fof(f147,plain,(
% 1.56/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.56/0.64    inference(cnf_transformation,[],[f78])).
% 1.56/0.64  fof(f78,plain,(
% 1.56/0.64    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.64    inference(ennf_transformation,[],[f33])).
% 1.56/0.64  fof(f33,axiom,(
% 1.56/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.56/0.64  fof(f1168,plain,(
% 1.56/0.64    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,sK3)),
% 1.56/0.64    inference(forward_demodulation,[],[f944,f319])).
% 1.56/0.64  fof(f319,plain,(
% 1.56/0.64    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.56/0.64    inference(resolution,[],[f311,f109])).
% 1.56/0.64  fof(f109,plain,(
% 1.56/0.64    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.56/0.64    inference(cnf_transformation,[],[f47])).
% 1.56/0.64  fof(f47,plain,(
% 1.56/0.64    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.56/0.64    inference(ennf_transformation,[],[f1])).
% 1.56/0.64  fof(f1,axiom,(
% 1.56/0.64    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.56/0.64  fof(f311,plain,(
% 1.56/0.64    v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.56/0.64    inference(resolution,[],[f308,f110])).
% 1.56/0.64  fof(f110,plain,(
% 1.56/0.64    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0))) )),
% 1.56/0.64    inference(cnf_transformation,[],[f48])).
% 1.56/0.64  fof(f48,plain,(
% 1.56/0.64    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 1.56/0.64    inference(ennf_transformation,[],[f16])).
% 1.56/0.64  fof(f16,axiom,(
% 1.56/0.64    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).
% 1.56/0.64  fof(f308,plain,(
% 1.56/0.64    v1_xboole_0(k1_xboole_0)),
% 1.56/0.64    inference(subsumption_resolution,[],[f306,f171])).
% 1.56/0.64  fof(f171,plain,(
% 1.56/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.64    inference(resolution,[],[f133,f103])).
% 1.56/0.64  fof(f133,plain,(
% 1.56/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.64    inference(cnf_transformation,[],[f89])).
% 1.56/0.64  fof(f89,plain,(
% 1.56/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.56/0.64    inference(nnf_transformation,[],[f13])).
% 1.56/0.64  fof(f13,axiom,(
% 1.56/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.64  fof(f306,plain,(
% 1.56/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | v1_xboole_0(k1_xboole_0)) )),
% 1.56/0.64    inference(resolution,[],[f303,f125])).
% 1.56/0.64  fof(f125,plain,(
% 1.56/0.64    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.56/0.64    inference(cnf_transformation,[],[f60])).
% 1.56/0.64  fof(f60,plain,(
% 1.56/0.64    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.56/0.64    inference(flattening,[],[f59])).
% 1.56/0.64  fof(f59,plain,(
% 1.56/0.64    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.56/0.64    inference(ennf_transformation,[],[f3])).
% 1.56/0.64  fof(f3,axiom,(
% 1.56/0.64    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.56/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.56/0.64  fof(f303,plain,(
% 1.56/0.64    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.56/0.64    inference(resolution,[],[f302,f122])).
% 1.56/0.64  fof(f122,plain,(
% 1.56/0.64    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.56/0.64    inference(cnf_transformation,[],[f86])).
% 1.56/0.65  % (5719)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.65  % (5727)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.14/0.66  % (5711)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.14/0.66  fof(f86,plain,(
% 2.14/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.14/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f85])).
% 2.14/0.66  fof(f85,plain,(
% 2.14/0.66    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f58,plain,(
% 2.14/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.14/0.66    inference(ennf_transformation,[],[f40])).
% 2.14/0.66  fof(f40,plain,(
% 2.14/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.14/0.66    inference(rectify,[],[f2])).
% 2.14/0.66  fof(f2,axiom,(
% 2.14/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.14/0.66  fof(f302,plain,(
% 2.14/0.66    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.14/0.66    inference(forward_demodulation,[],[f301,f102])).
% 2.14/0.66  fof(f102,plain,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.14/0.66    inference(cnf_transformation,[],[f23])).
% 2.14/0.66  fof(f23,axiom,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 2.14/0.66  fof(f301,plain,(
% 2.14/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f300,f106])).
% 2.14/0.66  fof(f106,plain,(
% 2.14/0.66    v1_relat_1(k1_xboole_0)),
% 2.14/0.66    inference(cnf_transformation,[],[f84])).
% 2.14/0.66  fof(f84,plain,(
% 2.14/0.66    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 2.14/0.66    inference(rectify,[],[f43])).
% 2.14/0.66  fof(f43,plain,(
% 2.14/0.66    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 2.14/0.66    inference(pure_predicate_removal,[],[f41])).
% 2.14/0.66  fof(f41,plain,(
% 2.14/0.66    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.14/0.66    inference(pure_predicate_removal,[],[f29])).
% 2.14/0.66  fof(f29,axiom,(
% 2.14/0.66    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 2.14/0.66  fof(f300,plain,(
% 2.14/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 2.14/0.66    inference(trivial_inequality_removal,[],[f299])).
% 2.14/0.66  fof(f299,plain,(
% 2.14/0.66    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 2.14/0.66    inference(superposition,[],[f127,f104])).
% 2.14/0.66  fof(f127,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f87])).
% 2.14/0.66  fof(f87,plain,(
% 2.14/0.66    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(nnf_transformation,[],[f62])).
% 2.14/0.66  fof(f62,plain,(
% 2.14/0.66    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f26])).
% 2.14/0.66  fof(f26,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 2.14/0.66  fof(f944,plain,(
% 2.14/0.66    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k4_relat_1(k1_xboole_0),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f863,f869])).
% 2.14/0.66  fof(f869,plain,(
% 2.14/0.66    k1_xboole_0 = sK2),
% 2.14/0.66    inference(resolution,[],[f840,f109])).
% 2.14/0.66  fof(f840,plain,(
% 2.14/0.66    v1_xboole_0(sK2)),
% 2.14/0.66    inference(resolution,[],[f830,f314])).
% 2.14/0.66  fof(f314,plain,(
% 2.14/0.66    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | v1_xboole_0(X2)) )),
% 2.14/0.66    inference(resolution,[],[f304,f125])).
% 2.14/0.66  fof(f304,plain,(
% 2.14/0.66    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 2.14/0.66    inference(resolution,[],[f302,f123])).
% 2.14/0.66  fof(f123,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f86])).
% 2.14/0.66  fof(f830,plain,(
% 2.14/0.66    r1_tarski(sK2,k1_xboole_0)),
% 2.14/0.66    inference(forward_demodulation,[],[f805,f152])).
% 2.14/0.66  fof(f152,plain,(
% 2.14/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.14/0.66    inference(equality_resolution,[],[f137])).
% 2.14/0.66  fof(f137,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.14/0.66    inference(cnf_transformation,[],[f91])).
% 2.14/0.66  fof(f91,plain,(
% 2.14/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.14/0.66    inference(flattening,[],[f90])).
% 2.14/0.66  fof(f90,plain,(
% 2.14/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.14/0.66    inference(nnf_transformation,[],[f11])).
% 2.14/0.66  fof(f11,axiom,(
% 2.14/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.14/0.66  fof(f805,plain,(
% 2.14/0.66    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))),
% 2.14/0.66    inference(backward_demodulation,[],[f385,f789])).
% 2.14/0.66  fof(f789,plain,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f788,f556])).
% 2.14/0.66  fof(f556,plain,(
% 2.14/0.66    ( ! [X5] : (k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X5) = k9_relat_1(sK2,X5)) )),
% 2.14/0.66    inference(forward_demodulation,[],[f551,f447])).
% 2.14/0.66  fof(f447,plain,(
% 2.14/0.66    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k4_relat_1(sK2),X0)) )),
% 2.14/0.66    inference(forward_demodulation,[],[f446,f249])).
% 2.14/0.66  fof(f249,plain,(
% 2.14/0.66    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f248,f184])).
% 2.14/0.66  fof(f184,plain,(
% 2.14/0.66    v1_relat_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f176,f169])).
% 2.14/0.66  fof(f169,plain,(
% 2.14/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 2.14/0.66    inference(backward_demodulation,[],[f163,f161])).
% 2.14/0.66  fof(f161,plain,(
% 2.14/0.66    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.14/0.66    inference(resolution,[],[f108,f93])).
% 2.14/0.66  fof(f93,plain,(
% 2.14/0.66    l1_struct_0(sK1)),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f83,plain,(
% 2.14/0.66    (((k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.14/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f82,f81,f80,f79])).
% 2.14/0.66  fof(f79,plain,(
% 2.14/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f80,plain,(
% 2.14/0.66    ? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f81,plain,(
% 2.14/0.66    ? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f82,plain,(
% 2.14/0.66    ? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f45,plain,(
% 2.14/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.14/0.66    inference(flattening,[],[f44])).
% 2.14/0.66  fof(f44,plain,(
% 2.14/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f39])).
% 2.14/0.66  fof(f39,negated_conjecture,(
% 2.14/0.66    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 2.14/0.66    inference(negated_conjecture,[],[f38])).
% 2.14/0.66  fof(f38,conjecture,(
% 2.14/0.66    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).
% 2.14/0.66  fof(f108,plain,(
% 2.14/0.66    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f46])).
% 2.14/0.66  fof(f46,plain,(
% 2.14/0.66    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f36])).
% 2.14/0.66  fof(f36,axiom,(
% 2.14/0.66    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.14/0.66  fof(f163,plain,(
% 2.14/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 2.14/0.66    inference(backward_demodulation,[],[f96,f160])).
% 2.14/0.66  fof(f160,plain,(
% 2.14/0.66    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.14/0.66    inference(resolution,[],[f108,f92])).
% 2.14/0.66  fof(f92,plain,(
% 2.14/0.66    l1_struct_0(sK0)),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f96,plain,(
% 2.14/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f176,plain,(
% 2.14/0.66    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_relat_1(X1)) )),
% 2.14/0.66    inference(resolution,[],[f114,f120])).
% 2.14/0.66  fof(f120,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.14/0.66    inference(cnf_transformation,[],[f17])).
% 2.14/0.66  fof(f17,axiom,(
% 2.14/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.14/0.66  fof(f114,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f51])).
% 2.14/0.66  fof(f51,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f15])).
% 2.14/0.66  fof(f15,axiom,(
% 2.14/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.14/0.66  fof(f248,plain,(
% 2.14/0.66    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f247,f94])).
% 2.14/0.66  fof(f94,plain,(
% 2.14/0.66    v1_funct_1(sK2)),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f247,plain,(
% 2.14/0.66    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f117,f99])).
% 2.14/0.66  fof(f99,plain,(
% 2.14/0.66    v2_funct_1(sK2)),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f117,plain,(
% 2.14/0.66    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f55])).
% 2.14/0.66  fof(f55,plain,(
% 2.14/0.66    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f54])).
% 2.14/0.66  fof(f54,plain,(
% 2.14/0.66    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f24])).
% 2.14/0.66  fof(f24,axiom,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.14/0.66  fof(f446,plain,(
% 2.14/0.66    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f445,f184])).
% 2.14/0.66  fof(f445,plain,(
% 2.14/0.66    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f444,f94])).
% 2.14/0.66  fof(f444,plain,(
% 2.14/0.66    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.14/0.66    inference(resolution,[],[f129,f99])).
% 2.14/0.66  fof(f129,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f64])).
% 2.14/0.66  fof(f64,plain,(
% 2.14/0.66    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(flattening,[],[f63])).
% 2.14/0.66  fof(f63,plain,(
% 2.14/0.66    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.14/0.66    inference(ennf_transformation,[],[f27])).
% 2.14/0.66  fof(f27,axiom,(
% 2.14/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 2.14/0.66  fof(f551,plain,(
% 2.14/0.66    ( ! [X5] : (k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X5) = k10_relat_1(k4_relat_1(sK2),X5)) )),
% 2.14/0.66    inference(resolution,[],[f507,f291])).
% 2.14/0.66  fof(f291,plain,(
% 2.14/0.66    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))),
% 2.14/0.66    inference(backward_demodulation,[],[f282,f290])).
% 2.14/0.66  fof(f290,plain,(
% 2.14/0.66    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 2.14/0.66    inference(forward_demodulation,[],[f289,f249])).
% 2.14/0.66  fof(f289,plain,(
% 2.14/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.14/0.66    inference(subsumption_resolution,[],[f288,f184])).
% 2.14/0.66  fof(f288,plain,(
% 2.14/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f287,f94])).
% 2.14/0.66  fof(f287,plain,(
% 2.14/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f119,f99])).
% 2.14/0.66  fof(f119,plain,(
% 2.14/0.66    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f57])).
% 2.14/0.66  fof(f57,plain,(
% 2.14/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f56])).
% 2.14/0.66  fof(f56,plain,(
% 2.14/0.66    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f28])).
% 2.14/0.66  fof(f28,axiom,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.14/0.66  fof(f282,plain,(
% 2.14/0.66    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))),
% 2.14/0.66    inference(subsumption_resolution,[],[f280,f255])).
% 2.14/0.66  fof(f255,plain,(
% 2.14/0.66    v1_relat_1(k4_relat_1(sK2))),
% 2.14/0.66    inference(subsumption_resolution,[],[f254,f184])).
% 2.14/0.66  fof(f254,plain,(
% 2.14/0.66    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f251,f94])).
% 2.14/0.66  fof(f251,plain,(
% 2.14/0.66    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(superposition,[],[f115,f249])).
% 2.14/0.66  fof(f115,plain,(
% 2.14/0.66    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f53])).
% 2.14/0.66  fof(f53,plain,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f52])).
% 2.14/0.66  fof(f52,plain,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f25])).
% 2.14/0.66  fof(f25,axiom,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.14/0.66  fof(f280,plain,(
% 2.14/0.66    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))) | ~v1_relat_1(k4_relat_1(sK2))),
% 2.14/0.66    inference(superposition,[],[f113,f275])).
% 2.14/0.66  fof(f275,plain,(
% 2.14/0.66    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 2.14/0.66    inference(forward_demodulation,[],[f274,f249])).
% 2.14/0.66  fof(f274,plain,(
% 2.14/0.66    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.14/0.66    inference(subsumption_resolution,[],[f273,f184])).
% 2.14/0.66  fof(f273,plain,(
% 2.14/0.66    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f272,f94])).
% 2.14/0.66  fof(f272,plain,(
% 2.14/0.66    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f118,f99])).
% 2.14/0.66  fof(f118,plain,(
% 2.14/0.66    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f57])).
% 2.14/0.66  fof(f113,plain,(
% 2.14/0.66    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f50])).
% 2.14/0.66  fof(f50,plain,(
% 2.14/0.66    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f22])).
% 2.14/0.66  fof(f22,axiom,(
% 2.14/0.66    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 2.14/0.66  fof(f507,plain,(
% 2.14/0.66    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 2.14/0.66    inference(resolution,[],[f147,f134])).
% 2.14/0.66  fof(f134,plain,(
% 2.14/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f89])).
% 2.14/0.66  fof(f788,plain,(
% 2.14/0.66    k9_relat_1(sK2,sK3) != k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),sK3) | k1_xboole_0 = k2_relat_1(sK2)),
% 2.14/0.66    inference(superposition,[],[f784,f660])).
% 2.14/0.66  fof(f660,plain,(
% 2.14/0.66    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f659,f184])).
% 2.14/0.66  fof(f659,plain,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f658,f206])).
% 2.14/0.66  fof(f206,plain,(
% 2.14/0.66    v4_relat_1(sK2,k2_struct_0(sK0))),
% 2.14/0.66    inference(resolution,[],[f140,f169])).
% 2.14/0.66  fof(f140,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f70])).
% 2.14/0.66  fof(f70,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.66    inference(ennf_transformation,[],[f42])).
% 2.14/0.66  fof(f42,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.14/0.66    inference(pure_predicate_removal,[],[f30])).
% 2.14/0.66  fof(f30,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.14/0.66  fof(f658,plain,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f657,f131])).
% 2.14/0.66  fof(f131,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f88])).
% 2.14/0.66  fof(f88,plain,(
% 2.14/0.66    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(nnf_transformation,[],[f68])).
% 2.14/0.66  fof(f68,plain,(
% 2.14/0.66    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(flattening,[],[f67])).
% 2.14/0.66  fof(f67,plain,(
% 2.14/0.66    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.14/0.66    inference(ennf_transformation,[],[f34])).
% 2.14/0.66  fof(f34,axiom,(
% 2.14/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 2.14/0.66  fof(f657,plain,(
% 2.14/0.66    v1_partfun1(sK2,k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f656,f94])).
% 2.14/0.66  fof(f656,plain,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f655,f383])).
% 2.14/0.66  fof(f383,plain,(
% 2.14/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 2.14/0.66    inference(backward_demodulation,[],[f169,f380])).
% 2.14/0.66  fof(f380,plain,(
% 2.14/0.66    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 2.14/0.66    inference(backward_demodulation,[],[f168,f376])).
% 2.14/0.66  fof(f376,plain,(
% 2.14/0.66    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f139,f169])).
% 2.14/0.66  fof(f139,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f69])).
% 2.14/0.66  fof(f69,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.66    inference(ennf_transformation,[],[f31])).
% 2.14/0.66  fof(f31,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.14/0.66  fof(f168,plain,(
% 2.14/0.66    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 2.14/0.66    inference(backward_demodulation,[],[f165,f161])).
% 2.14/0.66  fof(f165,plain,(
% 2.14/0.66    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 2.14/0.66    inference(backward_demodulation,[],[f98,f160])).
% 2.14/0.66  fof(f98,plain,(
% 2.14/0.66    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f655,plain,(
% 2.14/0.66    k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 2.14/0.66    inference(resolution,[],[f155,f384])).
% 2.14/0.66  fof(f384,plain,(
% 2.14/0.66    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 2.14/0.66    inference(backward_demodulation,[],[f170,f380])).
% 2.14/0.66  fof(f170,plain,(
% 2.14/0.66    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 2.14/0.66    inference(backward_demodulation,[],[f162,f161])).
% 2.14/0.66  fof(f162,plain,(
% 2.14/0.66    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 2.14/0.66    inference(backward_demodulation,[],[f95,f160])).
% 2.14/0.66  fof(f95,plain,(
% 2.14/0.66    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f155,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_funct_1(X2)) )),
% 2.14/0.66    inference(duplicate_literal_removal,[],[f142])).
% 2.14/0.66  fof(f142,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f74])).
% 2.14/0.66  fof(f74,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.14/0.66    inference(flattening,[],[f73])).
% 2.14/0.66  fof(f73,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.14/0.66    inference(ennf_transformation,[],[f35])).
% 2.14/0.66  fof(f35,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 2.14/0.66  fof(f784,plain,(
% 2.14/0.66    k9_relat_1(sK2,sK3) != k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f506,f783])).
% 2.14/0.66  fof(f783,plain,(
% 2.14/0.66    k4_relat_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f782,f383])).
% 2.14/0.66  fof(f782,plain,(
% 2.14/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | k4_relat_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 2.14/0.66    inference(subsumption_resolution,[],[f780,f388])).
% 2.14/0.66  fof(f388,plain,(
% 2.14/0.66    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 2.14/0.66    inference(backward_demodulation,[],[f376,f380])).
% 2.14/0.66  fof(f780,plain,(
% 2.14/0.66    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | k4_relat_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 2.14/0.66    inference(resolution,[],[f719,f384])).
% 2.14/0.66  fof(f719,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2)) )),
% 2.14/0.66    inference(forward_demodulation,[],[f718,f249])).
% 2.14/0.66  fof(f718,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f717,f94])).
% 2.14/0.66  fof(f717,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 2.14/0.66    inference(resolution,[],[f141,f99])).
% 2.14/0.66  fof(f141,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f72])).
% 2.14/0.66  fof(f72,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.14/0.66    inference(flattening,[],[f71])).
% 2.14/0.66  fof(f71,plain,(
% 2.14/0.66    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.14/0.66    inference(ennf_transformation,[],[f37])).
% 2.14/0.66  fof(f37,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 2.14/0.66  fof(f506,plain,(
% 2.14/0.66    k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),sK3) != k9_relat_1(sK2,sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f382,f502])).
% 2.14/0.66  fof(f502,plain,(
% 2.14/0.66    ( ! [X7] : (k7_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X7) = k9_relat_1(sK2,X7)) )),
% 2.14/0.66    inference(resolution,[],[f146,f383])).
% 2.14/0.66  fof(f146,plain,(
% 2.14/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f77])).
% 2.14/0.66  fof(f77,plain,(
% 2.14/0.66    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.66    inference(ennf_transformation,[],[f32])).
% 2.14/0.66  fof(f32,axiom,(
% 2.14/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.14/0.66  fof(f382,plain,(
% 2.14/0.66    k7_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK3) != k8_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f167,f380])).
% 2.14/0.66  fof(f167,plain,(
% 2.14/0.66    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f166,f161])).
% 2.14/0.66  fof(f166,plain,(
% 2.14/0.66    k7_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f100,f160])).
% 2.14/0.66  fof(f100,plain,(
% 2.14/0.66    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 2.14/0.66    inference(cnf_transformation,[],[f83])).
% 2.14/0.66  fof(f385,plain,(
% 2.14/0.66    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))),
% 2.14/0.66    inference(backward_demodulation,[],[f174,f380])).
% 2.14/0.66  fof(f174,plain,(
% 2.14/0.66    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 2.14/0.66    inference(resolution,[],[f169,f133])).
% 2.14/0.66  fof(f863,plain,(
% 2.14/0.66    k1_xboole_0 != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k4_relat_1(sK2),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f825,f856])).
% 2.14/0.66  fof(f856,plain,(
% 2.14/0.66    ( ! [X8] : (k1_xboole_0 = k9_relat_1(sK2,X8)) )),
% 2.14/0.66    inference(forward_demodulation,[],[f851,f789])).
% 2.14/0.66  fof(f851,plain,(
% 2.14/0.66    ( ! [X8] : (k2_relat_1(sK2) = k9_relat_1(sK2,X8)) )),
% 2.14/0.66    inference(backward_demodulation,[],[f221,f839])).
% 2.14/0.66  fof(f839,plain,(
% 2.14/0.66    ( ! [X0] : (sK2 = k7_relat_1(sK2,X0)) )),
% 2.14/0.66    inference(resolution,[],[f830,f236])).
% 2.14/0.66  fof(f236,plain,(
% 2.14/0.66    ( ! [X2,X1] : (~r1_tarski(X1,k1_xboole_0) | k7_relat_1(X1,X2) = X1) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f226,f179])).
% 2.14/0.66  fof(f179,plain,(
% 2.14/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_relat_1(X0)) )),
% 2.14/0.66    inference(resolution,[],[f175,f134])).
% 2.14/0.66  fof(f175,plain,(
% 2.14/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_relat_1(X0)) )),
% 2.14/0.66    inference(resolution,[],[f114,f106])).
% 2.14/0.66  fof(f226,plain,(
% 2.14/0.66    ( ! [X2,X1] : (k7_relat_1(X1,X2) = X1 | ~v1_relat_1(X1) | ~r1_tarski(X1,k1_xboole_0)) )),
% 2.14/0.66    inference(resolution,[],[f130,f209])).
% 2.14/0.66  fof(f209,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v4_relat_1(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.14/0.66    inference(resolution,[],[f207,f134])).
% 2.14/0.66  fof(f207,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 2.14/0.66    inference(superposition,[],[f140,f152])).
% 2.14/0.66  fof(f130,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f66])).
% 2.14/0.66  fof(f66,plain,(
% 2.14/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(flattening,[],[f65])).
% 2.14/0.66  fof(f65,plain,(
% 2.14/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.14/0.66    inference(ennf_transformation,[],[f21])).
% 2.14/0.66  fof(f21,axiom,(
% 2.14/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.14/0.66  fof(f221,plain,(
% 2.14/0.66    ( ! [X8] : (k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)) )),
% 2.14/0.66    inference(resolution,[],[f126,f184])).
% 2.14/0.66  fof(f126,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f61])).
% 2.14/0.66  fof(f61,plain,(
% 2.14/0.66    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f18])).
% 2.14/0.66  fof(f18,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.14/0.66  fof(f825,plain,(
% 2.14/0.66    k9_relat_1(sK2,sK3) != k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k4_relat_1(sK2),sK3)),
% 2.14/0.66    inference(backward_demodulation,[],[f784,f789])).
% 2.14/0.66  % SZS output end Proof for theBenchmark
% 2.14/0.66  % (5705)------------------------------
% 2.14/0.66  % (5705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (5705)Termination reason: Refutation
% 2.14/0.66  
% 2.14/0.66  % (5705)Memory used [KB]: 7036
% 2.14/0.66  % (5705)Time elapsed: 0.216 s
% 2.14/0.66  % (5705)------------------------------
% 2.14/0.66  % (5705)------------------------------
% 2.14/0.66  % (5697)Success in time 0.294 s
%------------------------------------------------------------------------------
