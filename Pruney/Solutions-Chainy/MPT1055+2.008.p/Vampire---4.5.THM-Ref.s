%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 457 expanded)
%              Number of leaves         :   21 ( 173 expanded)
%              Depth                    :   20
%              Number of atoms          :  359 (3983 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(subsumption_resolution,[],[f405,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f405,plain,(
    ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f187,f375])).

fof(f375,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f368,f240])).

fof(f240,plain,(
    ~ r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f239,f94])).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f42,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ? [X4] :
          ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(f239,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f238,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f238,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f235,f234])).

fof(f234,plain,(
    r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    inference(resolution,[],[f202,f100])).

fof(f100,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    inference(backward_demodulation,[],[f97,f92])).

fof(f92,plain,(
    ! [X1] : k7_relset_1(sK0,sK1,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f97,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(backward_demodulation,[],[f54,f91])).

fof(f91,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

% (18456)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f54,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f202,plain,(
    ~ r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f198,f104])).

fof(f104,plain,(
    ! [X2,X3] :
      ( r1_tarski(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3))
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

% (18459)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f198,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    inference(resolution,[],[f108,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4)
      | ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
      | ~ r1_tarski(k9_relat_1(sK2,sK3),X0) ) ),
    inference(resolution,[],[f99,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f99,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    inference(backward_demodulation,[],[f98,f92])).

fof(f98,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(backward_demodulation,[],[f55,f91])).

fof(f55,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X4] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X4)),X4) ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f105,plain,(
    ! [X4] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X4)),X4)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f235,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f202,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f368,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f214,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f82,f69])).

fof(f82,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f214,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f106,f134])).

fof(f134,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f133,f49])).

fof(f133,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f132,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f132,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f130,f51])).

fof(f130,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f91,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f106,plain,(
    ! [X5] : r1_tarski(k10_relat_1(sK2,X5),k1_relat_1(sK2)) ),
    inference(resolution,[],[f94,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f187,plain,(
    ~ r1_tarski(sK1,sK5(sK1)) ),
    inference(resolution,[],[f126,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f74,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:51:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (18454)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (18455)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (18469)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (18454)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (18461)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (18471)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (18463)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f444,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f405,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0))),
% 0.22/0.50    inference(backward_demodulation,[],[f187,f375])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f368,f240])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k1_relat_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f239,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f51,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f42,f41,f40,f39,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f15])).
% 0.22/0.50  fof(f15,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f238,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f235,f234])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.22/0.50    inference(resolution,[],[f202,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f97,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X1] : (k7_relset_1(sK0,sK1,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 0.22/0.50    inference(resolution,[],[f51,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f54,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 0.22/0.50    inference(resolution,[],[f51,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  % (18456)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.22/0.50    inference(subsumption_resolution,[],[f198,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) | ~r1_tarski(X2,X3)) )),
% 0.22/0.50    inference(resolution,[],[f94,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  % (18459)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.22/0.50    inference(resolution,[],[f108,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(k9_relat_1(sK2,sK3),X0)) )),
% 0.22/0.50    inference(resolution,[],[f99,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.22/0.50    inference(backward_demodulation,[],[f98,f92])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f55,f91])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X4] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X4)),X4)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f105,f49])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X4] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X4)),X4) | ~v1_funct_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f94,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f202,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.22/0.50  fof(f368,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | r1_tarski(sK3,k1_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f214,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK3,X0)) )),
% 0.22/0.50    inference(resolution,[],[f82,f69])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    r1_tarski(sK3,sK0)),
% 0.22/0.50    inference(resolution,[],[f52,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    r1_tarski(sK0,k1_relat_1(sK2)) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(superposition,[],[f106,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    sK0 = k10_relat_1(sK2,sK1) | k1_xboole_0 = sK1),
% 0.22/0.50    inference(subsumption_resolution,[],[f133,f49])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    sK0 = k10_relat_1(sK2,sK1) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    sK0 = k10_relat_1(sK2,sK1) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f130,f51])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    sK0 = k10_relat_1(sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(superposition,[],[f91,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X5] : (r1_tarski(k10_relat_1(sK2,X5),k1_relat_1(sK2))) )),
% 0.22/0.50    inference(resolution,[],[f94,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK5(sK1))),
% 0.22/0.50    inference(resolution,[],[f126,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0] : m1_subset_1(sK5(X0),X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK5(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f74,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK1)) )),
% 0.22/0.50    inference(resolution,[],[f48,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (18454)------------------------------
% 0.22/0.50  % (18454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18454)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (18454)Memory used [KB]: 1918
% 0.22/0.50  % (18454)Time elapsed: 0.074 s
% 0.22/0.50  % (18454)------------------------------
% 0.22/0.50  % (18454)------------------------------
% 0.22/0.50  % (18465)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (18446)Success in time 0.14 s
%------------------------------------------------------------------------------
