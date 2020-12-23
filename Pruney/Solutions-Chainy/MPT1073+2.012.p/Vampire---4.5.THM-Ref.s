%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:57 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 310 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  347 (1428 expanded)
%              Number of equality atoms :   79 ( 285 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(subsumption_resolution,[],[f125,f247])).

fof(f247,plain,(
    ! [X2] : r1_tarski(k2_relat_1(sK4),X2) ),
    inference(subsumption_resolution,[],[f240,f56])).

% (19216)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f240,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,sK5(k2_relat_1(sK4),X2))
      | r1_tarski(k2_relat_1(sK4),X2) ) ),
    inference(backward_demodulation,[],[f114,f232])).

fof(f232,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f228,f220])).

fof(f220,plain,
    ( r2_hidden(sK6(sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f127,f216])).

fof(f216,plain,
    ( sK2 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f212,f120])).

fof(f120,plain,(
    k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ! [X4] :
        ( sK1 != k1_funct_1(sK4,X4)
        | ~ m1_subset_1(X4,sK2) )
    & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK1 != k1_funct_1(sK4,X4)
          | ~ m1_subset_1(X4,sK2) )
      & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f212,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f211,f104])).

fof(f104,plain,(
    sP0(sK2,sK4,sK3) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f30,f33])).

% (19227)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f211,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ sP0(sK2,sK4,sK3) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f127,plain,(
    r2_hidden(sK6(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) ),
    inference(resolution,[],[f126,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK4))
      | r2_hidden(sK6(X0,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) ) ),
    inference(superposition,[],[f116,f97])).

fof(f97,plain,(
    k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(resolution,[],[f57,f93])).

fof(f93,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f69,f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
      | r2_hidden(sK6(X0,X1,sK4),X1) ) ),
    inference(resolution,[],[f67,f93])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f126,plain,(
    r2_hidden(sK1,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f54,f122])).

fof(f122,plain,(
    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f228,plain,
    ( ~ r2_hidden(sK6(sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f164,f216])).

fof(f164,plain,(
    ~ r2_hidden(sK6(sK1,k1_relat_1(sK4),sK4),sK2) ),
    inference(resolution,[],[f163,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f163,plain,(
    ~ m1_subset_1(sK6(sK1,k1_relat_1(sK4),sK4),sK2) ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK6(sK1,k1_relat_1(sK4),sK4),sK2) ),
    inference(superposition,[],[f55,f159])).

fof(f159,plain,(
    sK1 = k1_funct_1(sK4,sK6(sK1,k1_relat_1(sK4),sK4)) ),
    inference(subsumption_resolution,[],[f158,f93])).

fof(f158,plain,
    ( sK1 = k1_funct_1(sK4,sK6(sK1,k1_relat_1(sK4),sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f156,f51])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f156,plain,
    ( sK1 = k1_funct_1(sK4,sK6(sK1,k1_relat_1(sK4),sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f153,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f153,plain,(
    r2_hidden(k4_tarski(sK6(sK1,k1_relat_1(sK4),sK4),sK1),sK4) ),
    inference(resolution,[],[f151,f126])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK4))
      | r2_hidden(k4_tarski(sK6(X0,k1_relat_1(sK4),sK4),X0),sK4) ) ),
    inference(superposition,[],[f148,f97])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,sK4),X0),sK4) ) ),
    inference(resolution,[],[f66,f93])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X4] :
      ( sK1 != k1_funct_1(sK4,X4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK3,sK5(k2_relat_1(sK4),X2))
      | r1_tarski(k2_relat_1(sK4),X2) ) ),
    inference(resolution,[],[f111,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f111,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k2_relat_1(sK4),X4),sK3)
      | r1_tarski(k2_relat_1(sK4),X4) ) ),
    inference(resolution,[],[f99,f103])).

fof(f103,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(subsumption_resolution,[],[f102,f93])).

fof(f102,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f100,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f100,plain,(
    v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f72,f53])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f99,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | r2_hidden(sK5(X1,X2),X3)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    ~ r1_tarski(k2_relat_1(sK4),sK1) ),
    inference(backward_demodulation,[],[f89,f122])).

fof(f89,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(resolution,[],[f64,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19203)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (19222)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (19215)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (19229)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (19207)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (19215)Refutation not found, incomplete strategy% (19215)------------------------------
% 0.20/0.51  % (19215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19204)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (19206)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (19215)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19215)Memory used [KB]: 10746
% 0.20/0.51  % (19215)Time elapsed: 0.106 s
% 0.20/0.51  % (19215)------------------------------
% 0.20/0.51  % (19215)------------------------------
% 1.25/0.51  % (19217)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.52  % (19232)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.52  % (19210)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.52  % (19218)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.52  % (19221)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.52  % (19224)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.52  % (19233)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.52  % (19212)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (19205)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (19230)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.53  % (19210)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f249,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(subsumption_resolution,[],[f125,f247])).
% 1.25/0.53  fof(f247,plain,(
% 1.25/0.53    ( ! [X2] : (r1_tarski(k2_relat_1(sK4),X2)) )),
% 1.25/0.53    inference(subsumption_resolution,[],[f240,f56])).
% 1.25/0.53  % (19216)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.25/0.53  fof(f240,plain,(
% 1.25/0.53    ( ! [X2] : (~r1_tarski(k1_xboole_0,sK5(k2_relat_1(sK4),X2)) | r1_tarski(k2_relat_1(sK4),X2)) )),
% 1.25/0.53    inference(backward_demodulation,[],[f114,f232])).
% 1.25/0.53  fof(f232,plain,(
% 1.25/0.53    k1_xboole_0 = sK3),
% 1.25/0.53    inference(subsumption_resolution,[],[f228,f220])).
% 1.25/0.53  fof(f220,plain,(
% 1.25/0.53    r2_hidden(sK6(sK1,sK2,sK4),sK2) | k1_xboole_0 = sK3),
% 1.25/0.53    inference(superposition,[],[f127,f216])).
% 1.25/0.53  fof(f216,plain,(
% 1.25/0.53    sK2 = k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 1.25/0.53    inference(superposition,[],[f212,f120])).
% 1.25/0.53  fof(f120,plain,(
% 1.25/0.53    k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4)),
% 1.25/0.53    inference(resolution,[],[f70,f53])).
% 1.25/0.53  fof(f53,plain,(
% 1.25/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.25/0.53    inference(cnf_transformation,[],[f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ! [X4] : (sK1 != k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (sK1 != k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 1.25/0.53    inference(flattening,[],[f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 1.25/0.53    inference(ennf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.25/0.53    inference(negated_conjecture,[],[f14])).
% 1.25/0.53  fof(f14,conjecture,(
% 1.25/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 1.25/0.53  fof(f70,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.25/0.53  fof(f212,plain,(
% 1.25/0.53    sK2 = k1_relset_1(sK2,sK3,sK4) | k1_xboole_0 = sK3),
% 1.25/0.53    inference(subsumption_resolution,[],[f211,f104])).
% 1.25/0.53  fof(f104,plain,(
% 1.25/0.53    sP0(sK2,sK4,sK3)),
% 1.25/0.53    inference(resolution,[],[f77,f53])).
% 1.25/0.53  fof(f77,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f48])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(nnf_transformation,[],[f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(definition_folding,[],[f30,f33])).
% 1.25/0.53  % (19227)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.25/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(flattening,[],[f29])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.25/0.53  fof(f211,plain,(
% 1.25/0.53    sK2 = k1_relset_1(sK2,sK3,sK4) | k1_xboole_0 = sK3 | ~sP0(sK2,sK4,sK3)),
% 1.25/0.53    inference(resolution,[],[f73,f52])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    v1_funct_2(sK4,sK2,sK3)),
% 1.25/0.53    inference(cnf_transformation,[],[f36])).
% 1.25/0.53  fof(f73,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f47])).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.25/0.53    inference(rectify,[],[f46])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.25/0.53    inference(nnf_transformation,[],[f33])).
% 1.25/0.53  fof(f127,plain,(
% 1.25/0.53    r2_hidden(sK6(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))),
% 1.25/0.53    inference(resolution,[],[f126,f118])).
% 1.25/0.53  fof(f118,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK4)) | r2_hidden(sK6(X0,k1_relat_1(sK4),sK4),k1_relat_1(sK4))) )),
% 1.25/0.53    inference(superposition,[],[f116,f97])).
% 1.25/0.53  fof(f97,plain,(
% 1.25/0.53    k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)),
% 1.25/0.53    inference(resolution,[],[f57,f93])).
% 1.25/0.53  fof(f93,plain,(
% 1.25/0.53    v1_relat_1(sK4)),
% 1.25/0.53    inference(resolution,[],[f69,f53])).
% 1.25/0.53  fof(f69,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f19])).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.25/0.53  fof(f116,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK4,X1)) | r2_hidden(sK6(X0,X1,sK4),X1)) )),
% 1.25/0.53    inference(resolution,[],[f67,f93])).
% 1.25/0.53  fof(f67,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f45])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(rectify,[],[f42])).
% 1.25/0.53  fof(f42,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(nnf_transformation,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(ennf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.25/0.53  fof(f126,plain,(
% 1.25/0.53    r2_hidden(sK1,k2_relat_1(sK4))),
% 1.25/0.53    inference(backward_demodulation,[],[f54,f122])).
% 1.25/0.53  fof(f122,plain,(
% 1.25/0.53    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)),
% 1.25/0.53    inference(resolution,[],[f71,f53])).
% 1.25/0.53  fof(f71,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f12])).
% 1.25/0.53  fof(f12,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))),
% 1.25/0.53    inference(cnf_transformation,[],[f36])).
% 1.25/0.53  fof(f228,plain,(
% 1.25/0.53    ~r2_hidden(sK6(sK1,sK2,sK4),sK2) | k1_xboole_0 = sK3),
% 1.25/0.53    inference(superposition,[],[f164,f216])).
% 1.25/0.53  fof(f164,plain,(
% 1.25/0.53    ~r2_hidden(sK6(sK1,k1_relat_1(sK4),sK4),sK2)),
% 1.25/0.53    inference(resolution,[],[f163,f60])).
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.25/0.53  fof(f163,plain,(
% 1.25/0.53    ~m1_subset_1(sK6(sK1,k1_relat_1(sK4),sK4),sK2)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f162])).
% 1.25/0.53  fof(f162,plain,(
% 1.25/0.53    sK1 != sK1 | ~m1_subset_1(sK6(sK1,k1_relat_1(sK4),sK4),sK2)),
% 1.25/0.53    inference(superposition,[],[f55,f159])).
% 1.25/0.53  fof(f159,plain,(
% 1.25/0.53    sK1 = k1_funct_1(sK4,sK6(sK1,k1_relat_1(sK4),sK4))),
% 1.25/0.53    inference(subsumption_resolution,[],[f158,f93])).
% 1.25/0.53  fof(f158,plain,(
% 1.25/0.53    sK1 = k1_funct_1(sK4,sK6(sK1,k1_relat_1(sK4),sK4)) | ~v1_relat_1(sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f156,f51])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    v1_funct_1(sK4)),
% 1.25/0.53    inference(cnf_transformation,[],[f36])).
% 1.25/0.53  fof(f156,plain,(
% 1.25/0.53    sK1 = k1_funct_1(sK4,sK6(sK1,k1_relat_1(sK4),sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.25/0.53    inference(resolution,[],[f153,f81])).
% 1.25/0.53  fof(f81,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f50])).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(flattening,[],[f49])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(nnf_transformation,[],[f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.25/0.53    inference(flattening,[],[f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.25/0.53  fof(f153,plain,(
% 1.25/0.53    r2_hidden(k4_tarski(sK6(sK1,k1_relat_1(sK4),sK4),sK1),sK4)),
% 1.25/0.53    inference(resolution,[],[f151,f126])).
% 1.25/0.53  fof(f151,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK4)) | r2_hidden(k4_tarski(sK6(X0,k1_relat_1(sK4),sK4),X0),sK4)) )),
% 1.25/0.53    inference(superposition,[],[f148,f97])).
% 1.25/0.53  fof(f148,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK4,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,sK4),X0),sK4)) )),
% 1.25/0.53    inference(resolution,[],[f66,f93])).
% 1.25/0.53  fof(f66,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f45])).
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    ( ! [X4] : (sK1 != k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f36])).
% 1.25/0.53  fof(f114,plain,(
% 1.25/0.53    ( ! [X2] : (~r1_tarski(sK3,sK5(k2_relat_1(sK4),X2)) | r1_tarski(k2_relat_1(sK4),X2)) )),
% 1.25/0.53    inference(resolution,[],[f111,f64])).
% 1.25/0.53  fof(f64,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.25/0.53  fof(f111,plain,(
% 1.25/0.53    ( ! [X4] : (r2_hidden(sK5(k2_relat_1(sK4),X4),sK3) | r1_tarski(k2_relat_1(sK4),X4)) )),
% 1.25/0.53    inference(resolution,[],[f99,f103])).
% 1.25/0.53  fof(f103,plain,(
% 1.25/0.53    r1_tarski(k2_relat_1(sK4),sK3)),
% 1.25/0.53    inference(subsumption_resolution,[],[f102,f93])).
% 1.25/0.53  fof(f102,plain,(
% 1.25/0.53    r1_tarski(k2_relat_1(sK4),sK3) | ~v1_relat_1(sK4)),
% 1.25/0.53    inference(resolution,[],[f100,f58])).
% 1.25/0.53  fof(f58,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(nnf_transformation,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.25/0.53  fof(f100,plain,(
% 1.25/0.53    v5_relat_1(sK4,sK3)),
% 1.25/0.53    inference(resolution,[],[f72,f53])).
% 1.25/0.53  fof(f72,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f16])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.25/0.53    inference(pure_predicate_removal,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.25/0.53  fof(f99,plain,(
% 1.25/0.53    ( ! [X2,X3,X1] : (~r1_tarski(X1,X3) | r2_hidden(sK5(X1,X2),X3) | r1_tarski(X1,X2)) )),
% 1.25/0.53    inference(resolution,[],[f61,f62])).
% 1.25/0.53  fof(f62,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f41])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.53    inference(rectify,[],[f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.53    inference(nnf_transformation,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f41])).
% 1.25/0.53  fof(f125,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK4),sK1)),
% 1.25/0.53    inference(backward_demodulation,[],[f89,f122])).
% 1.25/0.53  fof(f89,plain,(
% 1.25/0.53    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 1.25/0.53    inference(resolution,[],[f64,f54])).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (19210)------------------------------
% 1.25/0.53  % (19210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (19210)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (19210)Memory used [KB]: 6524
% 1.25/0.53  % (19210)Time elapsed: 0.124 s
% 1.25/0.53  % (19210)------------------------------
% 1.25/0.53  % (19210)------------------------------
% 1.25/0.53  % (19226)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.53  % (19202)Success in time 0.173 s
%------------------------------------------------------------------------------
