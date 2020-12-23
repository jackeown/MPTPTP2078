%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 481 expanded)
%              Number of leaves         :   24 ( 155 expanded)
%              Depth                    :   15
%              Number of atoms          :  445 (3239 expanded)
%              Number of equality atoms :   61 ( 123 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f122,f133,f136,f154,f170,f174,f198,f281,f293,f365,f443])).

fof(f443,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f441,f236])).

fof(f236,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f235,f34])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
          | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
        & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
        & r1_tarski(sK1,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        & v1_funct_2(X4,sK0,sK3)
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
        | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
      & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      & v1_funct_2(sK4,sK0,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f235,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f234,f36])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f234,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_3 ),
    inference(superposition,[],[f74,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f74,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f441,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(resolution,[],[f414,f196])).

fof(f196,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(subsumption_resolution,[],[f195,f36])).

fof(f195,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(superposition,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f38,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f414,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k9_relat_1(sK4,sK1),X1)
        | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f296,f332])).

fof(f332,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f221,f37])).

fof(f37,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK4,X0)) = X0 )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f218,f83])).

fof(f83,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_4
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK4,X0)) = X0
        | ~ v1_relat_1(sK4) )
    | ~ spl5_9 ),
    inference(superposition,[],[f47,f203])).

fof(f203,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f199,f36])).

fof(f199,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_9 ),
    inference(superposition,[],[f106,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f106,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_9
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f296,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k9_relat_1(sK4,sK1),X1)
        | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),X1))) )
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f295,f123])).

fof(f123,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)
    | ~ spl5_4 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f295,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1)
        | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),X1))) )
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f294,f118])).

fof(f118,plain,(
    ! [X2] : k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f110,plain,(
    ! [X2] :
      ( k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f36,f42])).

fof(f294,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1) )
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f173,f118])).

fof(f173,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_12
  <=> ! [X1] :
        ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f365,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f363,f217])).

fof(f217,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f216,f34])).

fof(f216,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(sK4)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f206,f36])).

fof(f206,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_2 ),
    inference(superposition,[],[f70,f42])).

fof(f70,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f363,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(resolution,[],[f362,f196])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK4,sK1),X0)
        | v1_funct_2(k7_relat_1(sK4,sK1),sK1,X0) )
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f299,f332])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK4,sK1),X0)
        | v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),X0) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f298,f123])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X0)
        | v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),X0) )
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f297,f118])).

fof(f297,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) )
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f169,f118])).

fof(f169,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_11
  <=> ! [X0] :
        ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f293,plain,
    ( spl5_10
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f184,f263])).

fof(f263,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_10 ),
    inference(backward_demodulation,[],[f166,f118])).

fof(f166,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_10
  <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f184,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_13
  <=> v1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f281,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f271,f194])).

fof(f194,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_13 ),
    inference(resolution,[],[f185,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f185,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f271,plain,(
    ! [X2] : m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(subsumption_resolution,[],[f270,f34])).

fof(f270,plain,(
    ! [X2] :
      ( m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f269,f36])).

fof(f269,plain,(
    ! [X2] :
      ( m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f41,f118])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f198,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f174,plain,
    ( ~ spl5_10
    | spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f158,f64,f172,f164])).

fof(f64,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f158,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1)
        | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f65,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f170,plain,
    ( ~ spl5_10
    | spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f157,f64,f168,f164])).

fof(f157,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0)
        | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f152,f34])).

fof(f152,plain,
    ( ~ v1_funct_1(sK4)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f150,f36])).

fof(f150,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_1 ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f136,plain,
    ( ~ spl5_7
    | spl5_9
    | spl5_8 ),
    inference(avatar_split_clause,[],[f135,f100,f104,f96])).

fof(f100,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f135,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f134,f101])).

fof(f101,plain,
    ( k1_xboole_0 != sK3
    | spl5_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f134,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f35,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f33,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f33,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f115,f84])).

fof(f84,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f115,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f36,f55])).

fof(f75,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f39,f72,f68,f64])).

fof(f39,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (5018)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.45  % (5018)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f444,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f75,f122,f133,f136,f154,f170,f174,f198,f281,f293,f365,f443])).
% 0.22/0.45  fof(f443,plain,(
% 0.22/0.45    spl5_3 | ~spl5_4 | ~spl5_9 | ~spl5_12),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f442])).
% 0.22/0.45  fof(f442,plain,(
% 0.22/0.45    $false | (spl5_3 | ~spl5_4 | ~spl5_9 | ~spl5_12)),
% 0.22/0.45    inference(subsumption_resolution,[],[f441,f236])).
% 0.22/0.45  fof(f236,plain,(
% 0.22/0.45    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.22/0.45    inference(subsumption_resolution,[],[f235,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    v1_funct_1(sK4)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f30,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.22/0.45    inference(ennf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.22/0.45    inference(negated_conjecture,[],[f11])).
% 0.22/0.45  fof(f11,conjecture,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 0.22/0.45  fof(f235,plain,(
% 0.22/0.45    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | spl5_3),
% 0.22/0.45    inference(subsumption_resolution,[],[f234,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f234,plain,(
% 0.22/0.45    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_3),
% 0.22/0.45    inference(superposition,[],[f74,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.45    inference(flattening,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f72])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.45  fof(f441,plain,(
% 0.22/0.45    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_4 | ~spl5_9 | ~spl5_12)),
% 0.22/0.45    inference(resolution,[],[f414,f196])).
% 0.22/0.45  fof(f196,plain,(
% 0.22/0.45    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.22/0.45    inference(subsumption_resolution,[],[f195,f36])).
% 0.22/0.45  fof(f195,plain,(
% 0.22/0.45    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.22/0.45    inference(superposition,[],[f38,f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f414,plain,(
% 0.22/0.45    ( ! [X1] : (~r1_tarski(k9_relat_1(sK4,sK1),X1) | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl5_4 | ~spl5_9 | ~spl5_12)),
% 0.22/0.45    inference(forward_demodulation,[],[f296,f332])).
% 0.22/0.45  fof(f332,plain,(
% 0.22/0.45    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_9)),
% 0.22/0.45    inference(resolution,[],[f221,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    r1_tarski(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f221,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK4,X0)) = X0) ) | (~spl5_4 | ~spl5_9)),
% 0.22/0.45    inference(subsumption_resolution,[],[f218,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    v1_relat_1(sK4) | ~spl5_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f82])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl5_4 <=> v1_relat_1(sK4)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.45  fof(f218,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK4,X0)) = X0 | ~v1_relat_1(sK4)) ) | ~spl5_9),
% 0.22/0.45    inference(superposition,[],[f47,f203])).
% 0.22/0.45  fof(f203,plain,(
% 0.22/0.45    sK0 = k1_relat_1(sK4) | ~spl5_9),
% 0.22/0.45    inference(subsumption_resolution,[],[f199,f36])).
% 0.22/0.45  fof(f199,plain,(
% 0.22/0.45    sK0 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_9),
% 0.22/0.45    inference(superposition,[],[f106,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f104])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    spl5_9 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.45  fof(f296,plain,(
% 0.22/0.45    ( ! [X1] : (~r1_tarski(k9_relat_1(sK4,sK1),X1) | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),X1)))) ) | (~spl5_4 | ~spl5_12)),
% 0.22/0.45    inference(forward_demodulation,[],[f295,f123])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    ( ! [X0] : (k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)) ) | ~spl5_4),
% 0.22/0.45    inference(resolution,[],[f83,f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.45  fof(f295,plain,(
% 0.22/0.45    ( ! [X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),X1)))) ) | ~spl5_12),
% 0.22/0.45    inference(forward_demodulation,[],[f294,f118])).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    ( ! [X2] : (k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f110,f34])).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    ( ! [X2] : (k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2) | ~v1_funct_1(sK4)) )),
% 0.22/0.45    inference(resolution,[],[f36,f42])).
% 0.22/0.45  fof(f294,plain,(
% 0.22/0.45    ( ! [X1] : (m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1)) ) | ~spl5_12),
% 0.22/0.45    inference(forward_demodulation,[],[f173,f118])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1)) ) | ~spl5_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f172])).
% 0.22/0.45  fof(f172,plain,(
% 0.22/0.45    spl5_12 <=> ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.45  fof(f365,plain,(
% 0.22/0.45    spl5_2 | ~spl5_4 | ~spl5_9 | ~spl5_11),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f364])).
% 0.22/0.45  fof(f364,plain,(
% 0.22/0.45    $false | (spl5_2 | ~spl5_4 | ~spl5_9 | ~spl5_11)),
% 0.22/0.45    inference(subsumption_resolution,[],[f363,f217])).
% 0.22/0.45  fof(f217,plain,(
% 0.22/0.45    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_2),
% 0.22/0.45    inference(subsumption_resolution,[],[f216,f34])).
% 0.22/0.45  fof(f216,plain,(
% 0.22/0.45    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~v1_funct_1(sK4) | spl5_2),
% 0.22/0.45    inference(subsumption_resolution,[],[f206,f36])).
% 0.22/0.45  fof(f206,plain,(
% 0.22/0.45    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_2),
% 0.22/0.45    inference(superposition,[],[f70,f42])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f68])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.45  fof(f363,plain,(
% 0.22/0.45    v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_4 | ~spl5_9 | ~spl5_11)),
% 0.22/0.45    inference(resolution,[],[f362,f196])).
% 0.22/0.45  fof(f362,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(k9_relat_1(sK4,sK1),X0) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,X0)) ) | (~spl5_4 | ~spl5_9 | ~spl5_11)),
% 0.22/0.45    inference(forward_demodulation,[],[f299,f332])).
% 0.22/0.45  fof(f299,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(k9_relat_1(sK4,sK1),X0) | v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),X0)) ) | (~spl5_4 | ~spl5_11)),
% 0.22/0.45    inference(forward_demodulation,[],[f298,f123])).
% 0.22/0.45  fof(f298,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X0) | v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),X0)) ) | ~spl5_11),
% 0.22/0.45    inference(forward_demodulation,[],[f297,f118])).
% 0.22/0.45  fof(f297,plain,(
% 0.22/0.45    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,sK1),k1_relat_1(k7_relat_1(sK4,sK1)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0)) ) | ~spl5_11),
% 0.22/0.45    inference(forward_demodulation,[],[f169,f118])).
% 0.22/0.45  fof(f169,plain,(
% 0.22/0.45    ( ! [X0] : (v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0)) ) | ~spl5_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f168])).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    spl5_11 <=> ! [X0] : (v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.45  fof(f293,plain,(
% 0.22/0.45    spl5_10 | ~spl5_13),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f292])).
% 0.22/0.45  fof(f292,plain,(
% 0.22/0.45    $false | (spl5_10 | ~spl5_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f184,f263])).
% 0.22/0.45  fof(f263,plain,(
% 0.22/0.45    ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_10),
% 0.22/0.45    inference(backward_demodulation,[],[f166,f118])).
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f164])).
% 0.22/0.45  fof(f164,plain,(
% 0.22/0.45    spl5_10 <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.45  fof(f184,plain,(
% 0.22/0.45    v1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f183])).
% 0.22/0.45  fof(f183,plain,(
% 0.22/0.45    spl5_13 <=> v1_relat_1(k7_relat_1(sK4,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.45  fof(f281,plain,(
% 0.22/0.45    spl5_13),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f272])).
% 0.22/0.45  fof(f272,plain,(
% 0.22/0.45    $false | spl5_13),
% 0.22/0.45    inference(resolution,[],[f271,f194])).
% 0.22/0.45  fof(f194,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_13),
% 0.22/0.45    inference(resolution,[],[f185,f55])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.45  fof(f185,plain,(
% 0.22/0.45    ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f183])).
% 0.22/0.45  fof(f271,plain,(
% 0.22/0.45    ( ! [X2] : (m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f270,f34])).
% 0.22/0.45  fof(f270,plain,(
% 0.22/0.45    ( ! [X2] : (m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f269,f36])).
% 0.22/0.45  fof(f269,plain,(
% 0.22/0.45    ( ! [X2] : (m1_subset_1(k7_relat_1(sK4,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) )),
% 0.22/0.45    inference(superposition,[],[f41,f118])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    spl5_7),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.45  fof(f197,plain,(
% 0.22/0.45    $false | spl5_7),
% 0.22/0.45    inference(subsumption_resolution,[],[f98,f36])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | spl5_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f96])).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl5_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    ~spl5_10 | spl5_12 | ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f158,f64,f172,f164])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.45  fof(f158,plain,(
% 0.22/0.45    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))) ) | ~spl5_1),
% 0.22/0.45    inference(resolution,[],[f65,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~spl5_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f170,plain,(
% 0.22/0.45    ~spl5_10 | spl5_11 | ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f157,f64,f168,f164])).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    ( ! [X0] : (v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),X0) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))) ) | ~spl5_1),
% 0.22/0.45    inference(resolution,[],[f65,f45])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f154,plain,(
% 0.22/0.45    spl5_1),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f153])).
% 0.22/0.45  fof(f153,plain,(
% 0.22/0.45    $false | spl5_1),
% 0.22/0.45    inference(subsumption_resolution,[],[f152,f34])).
% 0.22/0.45  fof(f152,plain,(
% 0.22/0.45    ~v1_funct_1(sK4) | spl5_1),
% 0.22/0.45    inference(subsumption_resolution,[],[f150,f36])).
% 0.22/0.45  fof(f150,plain,(
% 0.22/0.45    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_1),
% 0.22/0.45    inference(resolution,[],[f66,f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    ~spl5_7 | spl5_9 | spl5_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f135,f100,f104,f96])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl5_8 <=> k1_xboole_0 = sK3),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.45  fof(f135,plain,(
% 0.22/0.45    sK0 = k1_relset_1(sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | spl5_8),
% 0.22/0.45    inference(subsumption_resolution,[],[f134,f101])).
% 0.22/0.45  fof(f101,plain,(
% 0.22/0.45    k1_xboole_0 != sK3 | spl5_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f100])).
% 0.22/0.45  fof(f134,plain,(
% 0.22/0.45    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.22/0.45    inference(resolution,[],[f35,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(nnf_transformation,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(flattening,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    v1_funct_2(sK4,sK0,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f133,plain,(
% 0.22/0.45    ~spl5_8),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    $false | ~spl5_8),
% 0.22/0.45    inference(subsumption_resolution,[],[f131,f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.45  fof(f131,plain,(
% 0.22/0.45    ~v1_xboole_0(k1_xboole_0) | ~spl5_8),
% 0.22/0.45    inference(backward_demodulation,[],[f33,f102])).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    k1_xboole_0 = sK3 | ~spl5_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f100])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~v1_xboole_0(sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    spl5_4),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f121])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    $false | spl5_4),
% 0.22/0.45    inference(subsumption_resolution,[],[f115,f84])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    ~v1_relat_1(sK4) | spl5_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f82])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    v1_relat_1(sK4)),
% 0.22/0.45    inference(resolution,[],[f36,f55])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f39,f72,f68,f64])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (5018)------------------------------
% 0.22/0.45  % (5018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (5018)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (5018)Memory used [KB]: 6268
% 0.22/0.45  % (5018)Time elapsed: 0.043 s
% 0.22/0.45  % (5018)------------------------------
% 0.22/0.45  % (5018)------------------------------
% 0.22/0.45  % (4998)Success in time 0.089 s
%------------------------------------------------------------------------------
