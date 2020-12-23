%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:13 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  104 (4168 expanded)
%              Number of leaves         :   12 ( 868 expanded)
%              Depth                    :   26
%              Number of atoms          :  267 (16442 expanded)
%              Number of equality atoms :   89 (2966 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(subsumption_resolution,[],[f425,f381])).

fof(f381,plain,(
    ~ r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f124,f368])).

fof(f368,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f162,f366])).

fof(f366,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | r2_hidden(sK5(sK4,sK2,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f326,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f326,plain,
    ( r2_hidden(sK5(sK4,sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f158,f315])).

fof(f315,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) != X0
      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f228,f104])).

fof(f104,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X1,k1_xboole_0),X3),k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = X1 ) ),
    inference(forward_demodulation,[],[f102,f74])).

fof(f74,plain,(
    ! [X4,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0) ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f102,plain,(
    ! [X2,X3,X1] :
      ( k1_relset_1(X1,X2,k1_xboole_0) = X1
      | ~ r2_hidden(k4_tarski(sK6(X1,k1_xboole_0),X3),k1_xboole_0) ) ),
    inference(resolution,[],[f53,f65])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | ~ r2_hidden(k4_tarski(sK6(X1,X2),X4),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f228,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | k1_relat_1(k1_xboole_0) != X0
      | r2_hidden(k4_tarski(sK6(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,sK6(k1_xboole_0,k1_xboole_0))),k1_xboole_0) ) ),
    inference(resolution,[],[f185,f108])).

fof(f108,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | k1_relat_1(k1_xboole_0) != X1
      | r2_hidden(k4_tarski(X3,sK7(k1_xboole_0,X3)),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f106,f74])).

fof(f106,plain,(
    ! [X2,X3,X1] :
      ( k1_relset_1(X1,X2,k1_xboole_0) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK7(k1_xboole_0,X3)),k1_xboole_0) ) ),
    inference(resolution,[],[f54,f65])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f185,plain,(
    ! [X0] :
      ( r2_hidden(sK6(k1_xboole_0,k1_xboole_0),X0)
      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f93,f72])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,k1_xboole_0),X0)
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f91,f74])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
      | r2_hidden(sK6(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f52,f65])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK6(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f158,plain,
    ( r2_hidden(sK5(sK4,sK2,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f83,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f139,f132])).

fof(f132,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f131])).

fof(f131,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f129,f124])).

fof(f129,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f83,f126])).

fof(f126,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f99,f71])).

fof(f71,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f99,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f97,f33])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

% (21577)Refutation not found, incomplete strategy% (21577)------------------------------
% (21577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f12])).

% (21577)Termination reason: Refutation not found, incomplete strategy
fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f34,f131])).

fof(f83,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f80,f68])).

fof(f68,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f67,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f80,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f78,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f31,f76])).

fof(f76,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f31,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f162,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,k1_xboole_0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f124,f150])).

fof(f124,plain,(
    ~ r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f109,f123])).

fof(f123,plain,(
    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f122,f68])).

fof(f122,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f117,f32])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f82,plain,(
    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f79,f68])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(resolution,[],[f84,f30])).

fof(f30,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f81,f68])).

fof(f81,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f425,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f83,f421])).

fof(f421,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f385,f420])).

fof(f420,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f408,f382])).

fof(f382,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f132,f368])).

fof(f408,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f383,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f383,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f133,f368])).

fof(f385,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f135,f368])).

fof(f135,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f71,f131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21590)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (21597)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21587)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (21579)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (21578)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21591)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (21577)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (21586)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (21583)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (21588)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (21580)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (21589)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (21595)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (21585)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (21588)Refutation not found, incomplete strategy% (21588)------------------------------
% 0.21/0.50  % (21588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21588)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21588)Memory used [KB]: 10618
% 0.21/0.50  % (21588)Time elapsed: 0.090 s
% 0.21/0.50  % (21588)------------------------------
% 0.21/0.50  % (21588)------------------------------
% 0.21/0.50  % (21581)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (21593)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (21582)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (21580)Refutation not found, incomplete strategy% (21580)------------------------------
% 0.21/0.51  % (21580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21592)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (21594)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (21596)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (21580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21580)Memory used [KB]: 11129
% 0.21/0.53  % (21580)Time elapsed: 0.099 s
% 0.21/0.53  % (21580)------------------------------
% 0.21/0.53  % (21580)------------------------------
% 1.32/0.53  % (21584)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.32/0.53  % (21594)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f437,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(subsumption_resolution,[],[f425,f381])).
% 1.32/0.53  fof(f381,plain,(
% 1.32/0.53    ~r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0)),
% 1.32/0.53    inference(backward_demodulation,[],[f124,f368])).
% 1.32/0.53  fof(f368,plain,(
% 1.32/0.53    k1_xboole_0 = sK0),
% 1.32/0.53    inference(subsumption_resolution,[],[f162,f366])).
% 1.32/0.53  fof(f366,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = sK0 | r2_hidden(sK5(sK4,sK2,k1_xboole_0),X0)) )),
% 1.32/0.53    inference(resolution,[],[f326,f72])).
% 1.32/0.53  fof(f72,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.32/0.53    inference(resolution,[],[f65,f38])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.32/0.53  fof(f65,plain,(
% 1.32/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.32/0.53    inference(resolution,[],[f39,f35])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f15])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.32/0.53    inference(unused_predicate_definition_removal,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.32/0.53  fof(f326,plain,(
% 1.32/0.53    r2_hidden(sK5(sK4,sK2,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0),
% 1.32/0.53    inference(backward_demodulation,[],[f158,f315])).
% 1.32/0.53  fof(f315,plain,(
% 1.32/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(equality_resolution,[],[f237])).
% 1.32/0.53  fof(f237,plain,(
% 1.32/0.53    ( ! [X0] : (k1_relat_1(k1_xboole_0) != X0 | k1_xboole_0 = k1_relat_1(k1_xboole_0)) )),
% 1.32/0.53    inference(subsumption_resolution,[],[f228,f104])).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    ( ! [X3,X1] : (~r2_hidden(k4_tarski(sK6(X1,k1_xboole_0),X3),k1_xboole_0) | k1_relat_1(k1_xboole_0) = X1) )),
% 1.32/0.53    inference(forward_demodulation,[],[f102,f74])).
% 1.32/0.53  fof(f74,plain,(
% 1.32/0.53    ( ! [X4,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f65,f45])).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.53    inference(ennf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.32/0.53  fof(f102,plain,(
% 1.32/0.53    ( ! [X2,X3,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = X1 | ~r2_hidden(k4_tarski(sK6(X1,k1_xboole_0),X3),k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f53,f65])).
% 1.32/0.53  fof(f53,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | ~r2_hidden(k4_tarski(sK6(X1,X2),X4),X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.32/0.53    inference(ennf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.32/0.53  fof(f228,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != X0 | r2_hidden(k4_tarski(sK6(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,sK6(k1_xboole_0,k1_xboole_0))),k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f185,f108])).
% 1.32/0.53  fof(f108,plain,(
% 1.32/0.53    ( ! [X3,X1] : (~r2_hidden(X3,X1) | k1_relat_1(k1_xboole_0) != X1 | r2_hidden(k4_tarski(X3,sK7(k1_xboole_0,X3)),k1_xboole_0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f106,f74])).
% 1.32/0.53  fof(f106,plain,(
% 1.32/0.53    ( ! [X2,X3,X1] : (k1_relset_1(X1,X2,k1_xboole_0) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK7(k1_xboole_0,X3)),k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f54,f65])).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f26])).
% 1.32/0.53  fof(f185,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK6(k1_xboole_0,k1_xboole_0),X0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f93,f72])).
% 1.32/0.53  fof(f93,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK6(X0,k1_xboole_0),X0) | k1_relat_1(k1_xboole_0) = X0) )),
% 1.32/0.53    inference(forward_demodulation,[],[f91,f74])).
% 1.32/0.53  fof(f91,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = X0 | r2_hidden(sK6(X0,k1_xboole_0),X0)) )),
% 1.32/0.53    inference(resolution,[],[f52,f65])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK6(X1,X2),X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f26])).
% 1.32/0.53  fof(f158,plain,(
% 1.32/0.53    r2_hidden(sK5(sK4,sK2,k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_xboole_0 = sK0),
% 1.32/0.53    inference(superposition,[],[f83,f150])).
% 1.32/0.53  fof(f150,plain,(
% 1.32/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 1.32/0.53    inference(subsumption_resolution,[],[f139,f132])).
% 1.32/0.53  fof(f132,plain,(
% 1.32/0.53    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.32/0.53    inference(backward_demodulation,[],[f33,f131])).
% 1.32/0.53  fof(f131,plain,(
% 1.32/0.53    k1_xboole_0 = sK1),
% 1.32/0.53    inference(subsumption_resolution,[],[f129,f124])).
% 1.32/0.53  fof(f129,plain,(
% 1.32/0.53    r2_hidden(sK5(sK4,sK2,sK3),sK0) | k1_xboole_0 = sK1),
% 1.32/0.53    inference(superposition,[],[f83,f126])).
% 1.32/0.53  fof(f126,plain,(
% 1.32/0.53    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.32/0.53    inference(superposition,[],[f99,f71])).
% 1.32/0.53  fof(f71,plain,(
% 1.32/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.32/0.53    inference(resolution,[],[f45,f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.53    inference(cnf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.32/0.53    inference(flattening,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.32/0.53    inference(ennf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.32/0.53    inference(negated_conjecture,[],[f13])).
% 1.32/0.53  fof(f13,conjecture,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 1.32/0.53  fof(f99,plain,(
% 1.32/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.32/0.53    inference(subsumption_resolution,[],[f97,f33])).
% 1.32/0.53  fof(f97,plain,(
% 1.32/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 1.32/0.53    inference(resolution,[],[f51,f34])).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.54  % (21577)Refutation not found, incomplete strategy% (21577)------------------------------
% 1.32/0.54  % (21577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.55    inference(flattening,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.55    inference(ennf_transformation,[],[f12])).
% 1.54/0.55  % (21577)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.55  fof(f12,axiom,(
% 1.54/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.54/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.54/0.55  fof(f33,plain,(
% 1.54/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.54/0.55    inference(cnf_transformation,[],[f17])).
% 1.54/0.55  fof(f139,plain,(
% 1.54/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.54/0.55    inference(resolution,[],[f133,f61])).
% 1.54/0.55  fof(f61,plain,(
% 1.54/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.54/0.55    inference(equality_resolution,[],[f47])).
% 1.54/0.55  fof(f47,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f25])).
% 1.54/0.55  fof(f133,plain,(
% 1.54/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.54/0.55    inference(backward_demodulation,[],[f34,f131])).
% 1.54/0.55  fof(f83,plain,(
% 1.54/0.55    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.54/0.55    inference(subsumption_resolution,[],[f80,f68])).
% 1.54/0.55  fof(f68,plain,(
% 1.54/0.55    v1_relat_1(sK3)),
% 1.54/0.55    inference(subsumption_resolution,[],[f67,f37])).
% 1.54/0.55  fof(f37,plain,(
% 1.54/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.54/0.55    inference(cnf_transformation,[],[f5])).
% 1.54/0.55  fof(f5,axiom,(
% 1.54/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.54/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.54/0.55  fof(f67,plain,(
% 1.54/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 1.54/0.55    inference(resolution,[],[f36,f34])).
% 1.54/0.55  fof(f36,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f18])).
% 1.54/0.55  fof(f18,plain,(
% 1.54/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.54/0.55    inference(ennf_transformation,[],[f4])).
% 1.54/0.55  fof(f4,axiom,(
% 1.54/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.54/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.54/0.55  fof(f80,plain,(
% 1.54/0.55    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.54/0.55    inference(resolution,[],[f78,f40])).
% 1.54/0.55  fof(f40,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f21])).
% 1.54/0.55  fof(f21,plain,(
% 1.54/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.54/0.55    inference(ennf_transformation,[],[f6])).
% 1.54/0.55  fof(f6,axiom,(
% 1.54/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.54/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.54/0.55  fof(f78,plain,(
% 1.54/0.55    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.54/0.55    inference(backward_demodulation,[],[f31,f76])).
% 1.54/0.55  fof(f76,plain,(
% 1.54/0.55    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.54/0.55    inference(resolution,[],[f58,f34])).
% 1.54/0.55  fof(f58,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f29])).
% 1.54/0.55  fof(f29,plain,(
% 1.54/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.55    inference(ennf_transformation,[],[f10])).
% 1.54/0.55  fof(f10,axiom,(
% 1.54/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.54/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.54/0.55  fof(f31,plain,(
% 1.54/0.55    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.54/0.55    inference(cnf_transformation,[],[f17])).
% 1.54/0.55  fof(f162,plain,(
% 1.54/0.55    ~r2_hidden(sK5(sK4,sK2,k1_xboole_0),sK0) | k1_xboole_0 = sK0),
% 1.54/0.55    inference(superposition,[],[f124,f150])).
% 1.54/0.55  fof(f124,plain,(
% 1.54/0.55    ~r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 1.54/0.55    inference(subsumption_resolution,[],[f109,f123])).
% 1.54/0.55  fof(f123,plain,(
% 1.54/0.55    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.54/0.55    inference(subsumption_resolution,[],[f122,f68])).
% 1.54/0.55  fof(f122,plain,(
% 1.54/0.55    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.54/0.55    inference(subsumption_resolution,[],[f117,f32])).
% 1.54/0.55  fof(f32,plain,(
% 1.54/0.55    v1_funct_1(sK3)),
% 1.54/0.55    inference(cnf_transformation,[],[f17])).
% 1.54/0.55  fof(f117,plain,(
% 1.54/0.55    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.54/0.55    inference(resolution,[],[f82,f56])).
% 1.54/0.55  fof(f56,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f28])).
% 1.54/0.55  fof(f28,plain,(
% 1.54/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.55    inference(flattening,[],[f27])).
% 1.54/0.55  fof(f27,plain,(
% 1.54/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.54/0.55    inference(ennf_transformation,[],[f7])).
% 1.54/0.55  fof(f7,axiom,(
% 1.54/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.54/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.54/0.55  fof(f82,plain,(
% 1.54/0.55    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 1.54/0.55    inference(subsumption_resolution,[],[f79,f68])).
% 1.54/0.55  fof(f79,plain,(
% 1.54/0.55    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.54/0.55    inference(resolution,[],[f78,f41])).
% 1.54/0.55  fof(f41,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f21])).
% 1.54/0.55  fof(f109,plain,(
% 1.54/0.55    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.54/0.55    inference(resolution,[],[f84,f30])).
% 1.54/0.55  fof(f30,plain,(
% 1.54/0.55    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f17])).
% 1.54/0.55  fof(f84,plain,(
% 1.54/0.55    r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 1.54/0.55    inference(subsumption_resolution,[],[f81,f68])).
% 1.54/0.55  fof(f81,plain,(
% 1.54/0.55    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.54/0.55    inference(resolution,[],[f78,f42])).
% 1.54/0.55  fof(f42,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f21])).
% 1.54/0.55  fof(f425,plain,(
% 1.54/0.55    r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0)),
% 1.54/0.55    inference(backward_demodulation,[],[f83,f421])).
% 1.54/0.55  fof(f421,plain,(
% 1.54/0.55    k1_xboole_0 = k1_relat_1(sK3)),
% 1.54/0.55    inference(backward_demodulation,[],[f385,f420])).
% 1.54/0.55  fof(f420,plain,(
% 1.54/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.54/0.55    inference(subsumption_resolution,[],[f408,f382])).
% 1.54/0.55  fof(f382,plain,(
% 1.54/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.54/0.55    inference(backward_demodulation,[],[f132,f368])).
% 1.54/0.55  fof(f408,plain,(
% 1.54/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.54/0.55    inference(resolution,[],[f383,f59])).
% 1.54/0.55  fof(f59,plain,(
% 1.54/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.54/0.55    inference(equality_resolution,[],[f49])).
% 1.54/0.55  fof(f49,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f25])).
% 1.54/0.55  fof(f383,plain,(
% 1.54/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.54/0.55    inference(backward_demodulation,[],[f133,f368])).
% 1.54/0.55  fof(f385,plain,(
% 1.54/0.55    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.54/0.55    inference(backward_demodulation,[],[f135,f368])).
% 1.54/0.55  fof(f135,plain,(
% 1.54/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 1.54/0.55    inference(backward_demodulation,[],[f71,f131])).
% 1.54/0.55  % SZS output end Proof for theBenchmark
% 1.54/0.55  % (21594)------------------------------
% 1.54/0.55  % (21594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (21594)Termination reason: Refutation
% 1.54/0.55  
% 1.54/0.55  % (21594)Memory used [KB]: 1918
% 1.54/0.55  % (21594)Time elapsed: 0.133 s
% 1.54/0.55  % (21594)------------------------------
% 1.54/0.55  % (21594)------------------------------
% 1.54/0.55  
% 1.54/0.55  % (21577)Memory used [KB]: 6524
% 1.54/0.55  % (21577)Time elapsed: 0.118 s
% 1.54/0.55  % (21577)------------------------------
% 1.54/0.55  % (21577)------------------------------
% 1.54/0.55  % (21576)Success in time 0.191 s
%------------------------------------------------------------------------------
