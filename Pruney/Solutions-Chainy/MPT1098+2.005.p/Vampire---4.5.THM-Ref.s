%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 162 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 ( 581 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f121,f455])).

fof(f455,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f453,f450])).

fof(f450,plain,(
    v1_finset_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f440,f310])).

fof(f310,plain,(
    ! [X1] : v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),X1))) ),
    inference(resolution,[],[f58,f98])).

fof(f98,plain,(
    v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f95,f31])).

fof(f31,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
        | ~ r1_tarski(X3,sK1)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
          | ~ r1_tarski(X3,sK1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(f95,plain,
    ( v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_finset_1(sK3(X0,X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ v1_finset_1(X1)
      | v1_finset_1(k1_relat_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f440,plain,
    ( ~ v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f299,f39])).

fof(f299,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f298,f122])).

fof(f122,plain,(
    v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f117,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,
    ( v1_relat_1(sK0)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f59,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f298,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f286,f37])).

fof(f286,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f116,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f116,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f113,f31])).

fof(f113,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f453,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f347,f315])).

fof(f315,plain,
    ( r1_tarski(k1_relat_1(sK0),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f89])).

fof(f89,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_4
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(k2_zfmisc_1(X4,X5)))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f347,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),sK1)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f346,f33])).

fof(f33,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f346,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),sK2)) ),
    inference(resolution,[],[f317,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f317,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),sK2))) ),
    inference(resolution,[],[f112,f59])).

fof(f112,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X4),X5))) ) ),
    inference(resolution,[],[f51,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f121,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f119,f37])).

fof(f119,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f117,f85])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f90,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f81,f87,f83])).

fof(f81,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f34,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:51:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (25821)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (25806)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (25810)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (25807)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (25820)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (25822)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (25823)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (25814)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (25815)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (25805)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (25808)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (25813)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (25812)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (25804)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (25817)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (25802)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.41/0.55  % (25827)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.55  % (25809)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.41/0.55  % (25825)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.41/0.55  % (25811)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.41/0.56  % (25826)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.41/0.56  % (25819)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.41/0.56  % (25818)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.56/0.57  % (25812)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f456,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f90,f121,f455])).
% 1.56/0.57  fof(f455,plain,(
% 1.56/0.57    ~spl5_4),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f454])).
% 1.56/0.57  fof(f454,plain,(
% 1.56/0.57    $false | ~spl5_4),
% 1.56/0.57    inference(subsumption_resolution,[],[f453,f450])).
% 1.56/0.57  fof(f450,plain,(
% 1.56/0.57    v1_finset_1(k1_relat_1(sK0))),
% 1.56/0.57    inference(subsumption_resolution,[],[f440,f310])).
% 1.56/0.57  fof(f310,plain,(
% 1.56/0.57    ( ! [X1] : (v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),X1)))) )),
% 1.56/0.57    inference(resolution,[],[f58,f98])).
% 1.56/0.57  fof(f98,plain,(
% 1.56/0.57    v1_finset_1(sK3(sK0,sK1,sK2))),
% 1.56/0.57    inference(subsumption_resolution,[],[f95,f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    v1_finset_1(sK0)),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f13,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.56/0.57    inference(negated_conjecture,[],[f11])).
% 1.56/0.57  fof(f11,conjecture,(
% 1.56/0.57    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).
% 1.56/0.57  fof(f95,plain,(
% 1.56/0.57    v1_finset_1(sK3(sK0,sK1,sK2)) | ~v1_finset_1(sK0)),
% 1.56/0.57    inference(resolution,[],[f46,f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_finset_1(sK3(X0,X1,X2)) | ~v1_finset_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f30])).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).
% 1.56/0.57  fof(f58,plain,(
% 1.56/0.57    ( ! [X2,X1] : (~v1_finset_1(X1) | v1_finset_1(k1_relat_1(k2_zfmisc_1(X1,X2)))) )),
% 1.56/0.57    inference(resolution,[],[f39,f38])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f18])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 1.56/0.57    inference(flattening,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(ennf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 1.56/0.57  fof(f440,plain,(
% 1.56/0.57    ~v1_finset_1(k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) | v1_finset_1(k1_relat_1(sK0))),
% 1.56/0.57    inference(resolution,[],[f299,f39])).
% 1.56/0.57  fof(f299,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))))),
% 1.56/0.57    inference(subsumption_resolution,[],[f298,f122])).
% 1.56/0.57  fof(f122,plain,(
% 1.56/0.57    v1_relat_1(sK0)),
% 1.56/0.57    inference(subsumption_resolution,[],[f117,f37])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.56/0.57  fof(f117,plain,(
% 1.56/0.57    v1_relat_1(sK0) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.56/0.57    inference(resolution,[],[f59,f36])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.56/0.57  fof(f59,plain,(
% 1.56/0.57    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.56/0.57    inference(resolution,[],[f44,f32])).
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.56/0.57    inference(nnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.57  fof(f298,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) | ~v1_relat_1(sK0)),
% 1.56/0.57    inference(subsumption_resolution,[],[f286,f37])).
% 1.56/0.57  fof(f286,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))) | ~v1_relat_1(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | ~v1_relat_1(sK0)),
% 1.56/0.57    inference(resolution,[],[f116,f34])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(flattening,[],[f14])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.56/0.57  fof(f116,plain,(
% 1.56/0.57    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))),
% 1.56/0.57    inference(subsumption_resolution,[],[f113,f31])).
% 1.56/0.57  fof(f113,plain,(
% 1.56/0.57    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | ~v1_finset_1(sK0)),
% 1.56/0.57    inference(resolution,[],[f50,f32])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) | ~v1_finset_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f30])).
% 1.56/0.57  fof(f453,plain,(
% 1.56/0.57    ~v1_finset_1(k1_relat_1(sK0)) | ~spl5_4),
% 1.56/0.57    inference(subsumption_resolution,[],[f347,f315])).
% 1.56/0.57  fof(f315,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),sK1) | ~spl5_4),
% 1.56/0.57    inference(resolution,[],[f76,f89])).
% 1.56/0.57  fof(f89,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_4),
% 1.56/0.57    inference(avatar_component_clause,[],[f87])).
% 1.56/0.57  fof(f87,plain,(
% 1.56/0.57    spl5_4 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2)))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.56/0.57  fof(f76,plain,(
% 1.56/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X3,k1_relat_1(k2_zfmisc_1(X4,X5))) | r1_tarski(X3,X4)) )),
% 1.56/0.57    inference(resolution,[],[f45,f38])).
% 1.56/0.57  fof(f45,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f20])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.57    inference(flattening,[],[f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(ennf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.56/0.57  fof(f347,plain,(
% 1.56/0.57    ~r1_tarski(k1_relat_1(sK0),sK1) | ~v1_finset_1(k1_relat_1(sK0))),
% 1.56/0.57    inference(resolution,[],[f346,f33])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f346,plain,(
% 1.56/0.57    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),sK2))),
% 1.56/0.57    inference(resolution,[],[f317,f43])).
% 1.56/0.57  fof(f43,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f28])).
% 1.56/0.57  fof(f317,plain,(
% 1.56/0.57    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),sK2)))),
% 1.56/0.57    inference(resolution,[],[f112,f59])).
% 1.56/0.57  fof(f112,plain,(
% 1.56/0.57    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X4),X5)))) )),
% 1.56/0.57    inference(resolution,[],[f51,f52])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.57    inference(equality_resolution,[],[f41])).
% 1.56/0.57  fof(f41,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(flattening,[],[f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f23])).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.56/0.57    inference(flattening,[],[f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.56/0.57    inference(ennf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 1.56/0.57  fof(f121,plain,(
% 1.56/0.57    spl5_3),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f120])).
% 1.56/0.57  fof(f120,plain,(
% 1.56/0.57    $false | spl5_3),
% 1.56/0.57    inference(subsumption_resolution,[],[f119,f37])).
% 1.56/0.57  fof(f119,plain,(
% 1.56/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl5_3),
% 1.56/0.57    inference(subsumption_resolution,[],[f117,f85])).
% 1.56/0.57  fof(f85,plain,(
% 1.56/0.57    ~v1_relat_1(sK0) | spl5_3),
% 1.56/0.57    inference(avatar_component_clause,[],[f83])).
% 1.56/0.57  fof(f83,plain,(
% 1.56/0.57    spl5_3 <=> v1_relat_1(sK0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.56/0.57  fof(f90,plain,(
% 1.56/0.57    ~spl5_3 | spl5_4),
% 1.56/0.57    inference(avatar_split_clause,[],[f81,f87,f83])).
% 1.56/0.57  fof(f81,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(sK0)),
% 1.56/0.57    inference(subsumption_resolution,[],[f77,f37])).
% 1.56/0.57  fof(f77,plain,(
% 1.56/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | ~v1_relat_1(sK0)),
% 1.56/0.57    inference(resolution,[],[f34,f32])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (25812)------------------------------
% 1.56/0.57  % (25812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (25812)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (25812)Memory used [KB]: 10874
% 1.56/0.57  % (25812)Time elapsed: 0.126 s
% 1.56/0.57  % (25812)------------------------------
% 1.56/0.57  % (25812)------------------------------
% 1.56/0.57  % (25801)Success in time 0.201 s
%------------------------------------------------------------------------------
