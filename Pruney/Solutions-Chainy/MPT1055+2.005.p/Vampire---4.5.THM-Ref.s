%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:13 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 300 expanded)
%              Number of leaves         :   22 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  416 (2573 expanded)
%              Number of equality atoms :   50 (  58 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f82,f114,f320,f344,f378])).

% (3993)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f378,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f350,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f350,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f42,f113])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f37,f36,f35,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(f344,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f342,f83])).

fof(f83,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f53,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f342,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f341,f121])).

fof(f121,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(superposition,[],[f110,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f110,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f341,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f340,f89])).

fof(f89,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f340,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f339,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f339,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f335,f322])).

fof(f322,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f321,f45])).

fof(f321,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_2 ),
    inference(superposition,[],[f78,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f78,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_2
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f335,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f334,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f334,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f326,f45])).

fof(f326,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1 ),
    inference(superposition,[],[f80,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f80,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_1
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f320,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f318,f94])).

fof(f94,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f93,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_1 ),
    inference(superposition,[],[f75,f67])).

fof(f75,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f318,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f317,f89])).

fof(f317,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f304,f43])).

fof(f304,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f172,f92])).

fof(f92,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f91,f45])).

fof(f91,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2 ),
    inference(superposition,[],[f81,f66])).

fof(f81,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(X0,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k9_relat_1(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k10_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f122,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k9_relat_1(X2,k10_relat_1(X2,X1)))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f87,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f114,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f107,f112,f109])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f106,f44])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f59,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f82,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f48,f77,f74])).

fof(f48,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f77,f74])).

fof(f49,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (824770560)
% 0.14/0.37  ipcrm: permission denied for id (824803336)
% 0.14/0.40  ipcrm: permission denied for id (824934434)
% 0.14/0.40  ipcrm: permission denied for id (824967203)
% 0.14/0.41  ipcrm: permission denied for id (825065510)
% 0.21/0.43  ipcrm: permission denied for id (825098297)
% 0.21/0.44  ipcrm: permission denied for id (825196611)
% 0.21/0.44  ipcrm: permission denied for id (825262150)
% 0.21/0.45  ipcrm: permission denied for id (825294923)
% 0.21/0.46  ipcrm: permission denied for id (825360470)
% 0.21/0.46  ipcrm: permission denied for id (825393239)
% 0.21/0.46  ipcrm: permission denied for id (825426008)
% 0.21/0.50  ipcrm: permission denied for id (825557108)
% 0.21/0.50  ipcrm: permission denied for id (825589883)
% 0.62/0.58  % (3995)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.78/0.59  % (3999)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.78/0.62  % (4000)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.78/0.63  % (3995)Refutation found. Thanks to Tanya!
% 0.78/0.63  % SZS status Theorem for theBenchmark
% 0.78/0.63  % SZS output start Proof for theBenchmark
% 0.78/0.63  fof(f380,plain,(
% 0.78/0.63    $false),
% 0.78/0.63    inference(avatar_sat_refutation,[],[f79,f82,f114,f320,f344,f378])).
% 0.78/0.63  % (3993)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.78/0.63  fof(f378,plain,(
% 0.78/0.63    ~spl5_4),
% 0.78/0.63    inference(avatar_contradiction_clause,[],[f377])).
% 0.78/0.63  fof(f377,plain,(
% 0.78/0.63    $false | ~spl5_4),
% 0.78/0.63    inference(subsumption_resolution,[],[f350,f50])).
% 0.78/0.63  fof(f50,plain,(
% 0.78/0.63    v1_xboole_0(k1_xboole_0)),
% 0.78/0.63    inference(cnf_transformation,[],[f1])).
% 0.78/0.63  fof(f1,axiom,(
% 0.78/0.63    v1_xboole_0(k1_xboole_0)),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.78/0.63  fof(f350,plain,(
% 0.78/0.63    ~v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 0.78/0.63    inference(backward_demodulation,[],[f42,f113])).
% 0.78/0.63  fof(f113,plain,(
% 0.78/0.63    k1_xboole_0 = sK1 | ~spl5_4),
% 0.78/0.63    inference(avatar_component_clause,[],[f112])).
% 0.78/0.63  fof(f112,plain,(
% 0.78/0.63    spl5_4 <=> k1_xboole_0 = sK1),
% 0.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.78/0.63  fof(f42,plain,(
% 0.78/0.63    ~v1_xboole_0(sK1)),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  fof(f38,plain,(
% 0.78/0.63    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.78/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f37,f36,f35,f34,f33])).
% 0.78/0.63  fof(f33,plain,(
% 0.78/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.78/0.63    introduced(choice_axiom,[])).
% 0.78/0.63  fof(f34,plain,(
% 0.78/0.63    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 0.78/0.63    introduced(choice_axiom,[])).
% 0.78/0.63  fof(f35,plain,(
% 0.78/0.63    ? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.78/0.63    introduced(choice_axiom,[])).
% 0.78/0.63  fof(f36,plain,(
% 0.78/0.63    ? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.78/0.63    introduced(choice_axiom,[])).
% 0.78/0.63  fof(f37,plain,(
% 0.78/0.63    ? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.78/0.63    introduced(choice_axiom,[])).
% 0.78/0.63  fof(f32,plain,(
% 0.78/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.78/0.63    inference(flattening,[],[f31])).
% 0.78/0.63  fof(f31,plain,(
% 0.78/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.78/0.63    inference(nnf_transformation,[],[f16])).
% 0.78/0.63  fof(f16,plain,(
% 0.78/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.78/0.63    inference(flattening,[],[f15])).
% 0.78/0.63  fof(f15,plain,(
% 0.78/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.78/0.63    inference(ennf_transformation,[],[f14])).
% 0.78/0.63  fof(f14,negated_conjecture,(
% 0.78/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.78/0.63    inference(negated_conjecture,[],[f13])).
% 0.78/0.63  fof(f13,conjecture,(
% 0.78/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).
% 0.78/0.63  fof(f344,plain,(
% 0.78/0.63    ~spl5_1 | spl5_2 | ~spl5_3),
% 0.78/0.63    inference(avatar_contradiction_clause,[],[f343])).
% 0.78/0.63  fof(f343,plain,(
% 0.78/0.63    $false | (~spl5_1 | spl5_2 | ~spl5_3)),
% 0.78/0.63    inference(subsumption_resolution,[],[f342,f83])).
% 0.78/0.63  fof(f83,plain,(
% 0.78/0.63    r1_tarski(sK3,sK0)),
% 0.78/0.63    inference(resolution,[],[f53,f46])).
% 0.78/0.63  fof(f46,plain,(
% 0.78/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  fof(f53,plain,(
% 0.78/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f39])).
% 0.78/0.63  fof(f39,plain,(
% 0.78/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.78/0.63    inference(nnf_transformation,[],[f4])).
% 0.78/0.63  fof(f4,axiom,(
% 0.78/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.78/0.63  fof(f342,plain,(
% 0.78/0.63    ~r1_tarski(sK3,sK0) | (~spl5_1 | spl5_2 | ~spl5_3)),
% 0.78/0.63    inference(forward_demodulation,[],[f341,f121])).
% 0.78/0.63  fof(f121,plain,(
% 0.78/0.63    sK0 = k1_relat_1(sK2) | ~spl5_3),
% 0.78/0.63    inference(subsumption_resolution,[],[f117,f45])).
% 0.78/0.63  fof(f45,plain,(
% 0.78/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  fof(f117,plain,(
% 0.78/0.63    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.78/0.63    inference(superposition,[],[f110,f58])).
% 0.78/0.63  fof(f58,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.78/0.63    inference(cnf_transformation,[],[f24])).
% 0.78/0.63  fof(f24,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(ennf_transformation,[],[f9])).
% 0.78/0.63  fof(f9,axiom,(
% 0.78/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.78/0.63  fof(f110,plain,(
% 0.78/0.63    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_3),
% 0.78/0.63    inference(avatar_component_clause,[],[f109])).
% 0.78/0.63  fof(f109,plain,(
% 0.78/0.63    spl5_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.78/0.63  fof(f341,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | spl5_2)),
% 0.78/0.63    inference(subsumption_resolution,[],[f340,f89])).
% 0.78/0.63  fof(f89,plain,(
% 0.78/0.63    v1_relat_1(sK2)),
% 0.78/0.63    inference(resolution,[],[f57,f45])).
% 0.78/0.63  fof(f57,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f23])).
% 0.78/0.63  fof(f23,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(ennf_transformation,[],[f8])).
% 0.78/0.63  fof(f8,axiom,(
% 0.78/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.78/0.63  fof(f340,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_1 | spl5_2)),
% 0.78/0.63    inference(subsumption_resolution,[],[f339,f43])).
% 0.78/0.63  fof(f43,plain,(
% 0.78/0.63    v1_funct_1(sK2)),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  fof(f339,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_1 | spl5_2)),
% 0.78/0.63    inference(subsumption_resolution,[],[f335,f322])).
% 0.78/0.63  fof(f322,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_2),
% 0.78/0.63    inference(subsumption_resolution,[],[f321,f45])).
% 0.78/0.63  fof(f321,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_2),
% 0.78/0.63    inference(superposition,[],[f78,f66])).
% 0.78/0.63  fof(f66,plain,(
% 0.78/0.63    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.78/0.63    inference(cnf_transformation,[],[f29])).
% 0.78/0.63  fof(f29,plain,(
% 0.78/0.63    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(ennf_transformation,[],[f11])).
% 0.78/0.63  fof(f11,axiom,(
% 0.78/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.78/0.63  fof(f78,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl5_2),
% 0.78/0.63    inference(avatar_component_clause,[],[f77])).
% 0.78/0.63  fof(f77,plain,(
% 0.78/0.63    spl5_2 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.78/0.63  fof(f335,plain,(
% 0.78/0.63    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_1),
% 0.78/0.63    inference(resolution,[],[f334,f65])).
% 0.78/0.63  fof(f65,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f28])).
% 0.78/0.63  fof(f28,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.78/0.63    inference(flattening,[],[f27])).
% 0.78/0.63  fof(f27,plain,(
% 0.78/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.78/0.63    inference(ennf_transformation,[],[f7])).
% 0.78/0.63  fof(f7,axiom,(
% 0.78/0.63    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.78/0.63  fof(f334,plain,(
% 0.78/0.63    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_1),
% 0.78/0.63    inference(subsumption_resolution,[],[f326,f45])).
% 0.78/0.63  fof(f326,plain,(
% 0.78/0.63    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_1),
% 0.78/0.63    inference(superposition,[],[f80,f67])).
% 0.78/0.63  fof(f67,plain,(
% 0.78/0.63    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.78/0.63    inference(cnf_transformation,[],[f30])).
% 0.78/0.63  fof(f30,plain,(
% 0.78/0.63    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(ennf_transformation,[],[f10])).
% 0.78/0.63  fof(f10,axiom,(
% 0.78/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.78/0.63  fof(f80,plain,(
% 0.78/0.63    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_1),
% 0.78/0.63    inference(avatar_component_clause,[],[f74])).
% 0.78/0.63  fof(f74,plain,(
% 0.78/0.63    spl5_1 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.78/0.63  fof(f320,plain,(
% 0.78/0.63    spl5_1 | ~spl5_2),
% 0.78/0.63    inference(avatar_contradiction_clause,[],[f319])).
% 0.78/0.63  fof(f319,plain,(
% 0.78/0.63    $false | (spl5_1 | ~spl5_2)),
% 0.78/0.63    inference(subsumption_resolution,[],[f318,f94])).
% 0.78/0.63  fof(f94,plain,(
% 0.78/0.63    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_1),
% 0.78/0.63    inference(subsumption_resolution,[],[f93,f45])).
% 0.78/0.63  fof(f93,plain,(
% 0.78/0.63    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_1),
% 0.78/0.63    inference(superposition,[],[f75,f67])).
% 0.78/0.63  fof(f75,plain,(
% 0.78/0.63    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl5_1),
% 0.78/0.63    inference(avatar_component_clause,[],[f74])).
% 0.78/0.63  fof(f318,plain,(
% 0.78/0.63    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_2),
% 0.78/0.63    inference(subsumption_resolution,[],[f317,f89])).
% 0.78/0.63  fof(f317,plain,(
% 0.78/0.63    ~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_2),
% 0.78/0.63    inference(subsumption_resolution,[],[f304,f43])).
% 0.78/0.63  fof(f304,plain,(
% 0.78/0.63    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_2),
% 0.78/0.63    inference(resolution,[],[f172,f92])).
% 0.78/0.63  fof(f92,plain,(
% 0.78/0.63    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_2),
% 0.78/0.63    inference(subsumption_resolution,[],[f91,f45])).
% 0.78/0.63  fof(f91,plain,(
% 0.78/0.63    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_2),
% 0.78/0.63    inference(superposition,[],[f81,f66])).
% 0.78/0.63  fof(f81,plain,(
% 0.78/0.63    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_2),
% 0.78/0.63    inference(avatar_component_clause,[],[f77])).
% 0.78/0.63  fof(f172,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,k10_relat_1(X0,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k9_relat_1(X0,X1),X2)) )),
% 0.78/0.63    inference(duplicate_literal_removal,[],[f170])).
% 0.78/0.63  fof(f170,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,X1),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(X1,k10_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.78/0.63    inference(resolution,[],[f122,f55])).
% 0.78/0.63  fof(f55,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f21])).
% 0.78/0.63  fof(f21,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.78/0.63    inference(flattening,[],[f20])).
% 0.78/0.63  fof(f20,plain,(
% 0.78/0.63    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.78/0.63    inference(ennf_transformation,[],[f5])).
% 0.78/0.63  fof(f5,axiom,(
% 0.78/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.78/0.63  fof(f122,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k9_relat_1(X2,k10_relat_1(X2,X1))) | r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.78/0.63    inference(resolution,[],[f87,f52])).
% 0.78/0.63  fof(f52,plain,(
% 0.78/0.63    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f19])).
% 0.78/0.63  fof(f19,plain,(
% 0.78/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.78/0.63    inference(flattening,[],[f18])).
% 0.78/0.63  fof(f18,plain,(
% 0.78/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.78/0.63    inference(ennf_transformation,[],[f6])).
% 0.78/0.63  fof(f6,axiom,(
% 0.78/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.78/0.63  fof(f87,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.78/0.63    inference(superposition,[],[f56,f51])).
% 0.78/0.63  fof(f51,plain,(
% 0.78/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f17])).
% 0.78/0.63  fof(f17,plain,(
% 0.78/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.78/0.63    inference(ennf_transformation,[],[f3])).
% 0.78/0.63  fof(f3,axiom,(
% 0.78/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.78/0.63  fof(f56,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.78/0.63    inference(cnf_transformation,[],[f22])).
% 0.78/0.63  fof(f22,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.78/0.63    inference(ennf_transformation,[],[f2])).
% 0.78/0.63  fof(f2,axiom,(
% 0.78/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.78/0.63  fof(f114,plain,(
% 0.78/0.63    spl5_3 | spl5_4),
% 0.78/0.63    inference(avatar_split_clause,[],[f107,f112,f109])).
% 0.78/0.63  fof(f107,plain,(
% 0.78/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.78/0.63    inference(subsumption_resolution,[],[f106,f44])).
% 0.78/0.63  fof(f44,plain,(
% 0.78/0.63    v1_funct_2(sK2,sK0,sK1)),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  fof(f106,plain,(
% 0.78/0.63    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.78/0.63    inference(resolution,[],[f59,f45])).
% 0.78/0.63  fof(f59,plain,(
% 0.78/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.78/0.63    inference(cnf_transformation,[],[f40])).
% 0.78/0.63  fof(f40,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(nnf_transformation,[],[f26])).
% 0.78/0.63  fof(f26,plain,(
% 0.78/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(flattening,[],[f25])).
% 0.78/0.63  fof(f25,plain,(
% 0.78/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.78/0.63    inference(ennf_transformation,[],[f12])).
% 0.78/0.63  fof(f12,axiom,(
% 0.78/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.78/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.78/0.63  fof(f82,plain,(
% 0.78/0.63    spl5_1 | spl5_2),
% 0.78/0.63    inference(avatar_split_clause,[],[f48,f77,f74])).
% 0.78/0.63  fof(f48,plain,(
% 0.78/0.63    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  fof(f79,plain,(
% 0.78/0.63    ~spl5_1 | ~spl5_2),
% 0.78/0.63    inference(avatar_split_clause,[],[f49,f77,f74])).
% 0.78/0.63  fof(f49,plain,(
% 0.78/0.63    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.78/0.63    inference(cnf_transformation,[],[f38])).
% 0.78/0.63  % SZS output end Proof for theBenchmark
% 0.78/0.63  % (3995)------------------------------
% 0.78/0.63  % (3995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.78/0.63  % (3995)Termination reason: Refutation
% 0.78/0.63  
% 0.78/0.63  % (3995)Memory used [KB]: 10874
% 0.78/0.63  % (3995)Time elapsed: 0.063 s
% 0.78/0.63  % (3995)------------------------------
% 0.78/0.63  % (3995)------------------------------
% 0.78/0.63  % (3858)Success in time 0.271 s
%------------------------------------------------------------------------------
