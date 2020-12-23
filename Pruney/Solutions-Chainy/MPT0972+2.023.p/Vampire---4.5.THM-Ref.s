%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:08 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  124 (1803 expanded)
%              Number of leaves         :   18 ( 533 expanded)
%              Depth                    :   25
%              Number of atoms          :  448 (12481 expanded)
%              Number of equality atoms :  160 (2631 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(subsumption_resolution,[],[f395,f341])).

fof(f341,plain,(
    ! [X4] : r2_relset_1(X4,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f291,f301])).

fof(f301,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f295,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f106,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f106,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f104,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f64,f97])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f295,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f288,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f288,plain,(
    ! [X1] : ~ r2_hidden(X1,sK3) ),
    inference(resolution,[],[f284,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f80,f57])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f284,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f274,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f274,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f51,f272])).

fof(f272,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f255,f121])).

fof(f121,plain,(
    r2_relset_1(sK1,sK2,sK3,sK3) ),
    inference(resolution,[],[f93,f51])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f255,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f56,f251])).

fof(f251,plain,
    ( sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f250,f214])).

fof(f214,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(resolution,[],[f211,f55])).

fof(f55,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK1,sK2,sK3,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
            | ~ r2_hidden(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
      & ! [X4] :
          ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
          | ~ r2_hidden(X4,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f211,plain,
    ( r2_hidden(sK5(sK3,sK4),sK1)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f210,f147])).

fof(f147,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f144,f129])).

fof(f129,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f144,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f142,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f73,f116])).

fof(f116,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f210,plain,
    ( sK1 != k1_relat_1(sK4)
    | r2_hidden(sK5(sK3,sK4),sK1)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f209,f101])).

fof(f101,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f71,f54])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f209,plain,
    ( sK1 != k1_relat_1(sK4)
    | r2_hidden(sK5(sK3,sK4),sK1)
    | ~ v1_relat_1(sK4)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f180,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f180,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK3,X0),sK1)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f162,f145])).

fof(f145,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f143,f128])).

fof(f128,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f72,f51])).

fof(f143,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f141,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f73,f115])).

fof(f115,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f77,f51])).

fof(f162,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),k1_relat_1(sK3))
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f100,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f71,f51])).

fof(f160,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),k1_relat_1(sK3))
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f250,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f249,f145])).

fof(f249,plain,
    ( sK1 != k1_relat_1(sK3)
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f248,f147])).

fof(f248,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK3)
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4 ),
    inference(subsumption_resolution,[],[f247,f101])).

fof(f247,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK3)
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | sK3 = sK4 ),
    inference(resolution,[],[f220,f52])).

fof(f220,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0))
      | ~ v1_relat_1(X0)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f218,f100])).

fof(f218,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0))
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f59,f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f291,plain,(
    ! [X4] : r2_relset_1(X4,k1_xboole_0,sK3,sK3) ),
    inference(resolution,[],[f284,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | r2_relset_1(X0,k1_xboole_0,X1,X1) ) ),
    inference(superposition,[],[f93,f85])).

fof(f395,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f336,f387])).

fof(f387,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f383,f109])).

fof(f383,plain,(
    v1_xboole_0(sK4) ),
    inference(resolution,[],[f376,f61])).

fof(f376,plain,(
    ! [X1] : ~ r2_hidden(X1,sK4) ),
    inference(resolution,[],[f285,f112])).

fof(f285,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f276,f85])).

fof(f276,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f54,f272])).

fof(f336,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f277,f301])).

fof(f277,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK3,sK4) ),
    inference(backward_demodulation,[],[f56,f272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (9210)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.53  % (9226)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (9218)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (9220)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (9204)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.55  % (9203)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.55  % (9212)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (9205)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.55  % (9206)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.56  % (9207)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.56  % (9221)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.56  % (9225)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.56  % (9230)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.56  % (9217)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.57  % (9228)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.57  % (9220)Refutation not found, incomplete strategy% (9220)------------------------------
% 1.50/0.57  % (9220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (9220)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (9220)Memory used [KB]: 10746
% 1.50/0.57  % (9220)Time elapsed: 0.139 s
% 1.50/0.57  % (9220)------------------------------
% 1.50/0.57  % (9220)------------------------------
% 1.50/0.57  % (9222)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.57  % (9213)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.57  % (9210)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f413,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(subsumption_resolution,[],[f395,f341])).
% 1.50/0.57  fof(f341,plain,(
% 1.50/0.57    ( ! [X4] : (r2_relset_1(X4,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 1.50/0.57    inference(backward_demodulation,[],[f291,f301])).
% 1.50/0.57  fof(f301,plain,(
% 1.50/0.57    k1_xboole_0 = sK3),
% 1.50/0.57    inference(resolution,[],[f295,f109])).
% 1.50/0.57  fof(f109,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.50/0.57    inference(resolution,[],[f106,f97])).
% 1.50/0.57  fof(f97,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.50/0.57    inference(resolution,[],[f66,f60])).
% 1.50/0.57  fof(f60,plain,(
% 1.50/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f36])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f34,plain,(
% 1.50/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.50/0.57    inference(rectify,[],[f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.50/0.57    inference(nnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.50/0.57  fof(f66,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f42])).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.57    inference(rectify,[],[f39])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.57    inference(nnf_transformation,[],[f18])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.57  fof(f106,plain,(
% 1.50/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.50/0.57    inference(resolution,[],[f104,f57])).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    v1_xboole_0(k1_xboole_0)),
% 1.50/0.57    inference(cnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    v1_xboole_0(k1_xboole_0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.50/0.57  fof(f104,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(resolution,[],[f64,f97])).
% 1.50/0.57  fof(f64,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f38])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.57    inference(flattening,[],[f37])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.57    inference(nnf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.57  fof(f295,plain,(
% 1.50/0.57    v1_xboole_0(sK3)),
% 1.50/0.57    inference(resolution,[],[f288,f61])).
% 1.50/0.57  fof(f61,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f36])).
% 1.50/0.57  fof(f288,plain,(
% 1.50/0.57    ( ! [X1] : (~r2_hidden(X1,sK3)) )),
% 1.50/0.57    inference(resolution,[],[f284,f112])).
% 1.50/0.57  fof(f112,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.50/0.57    inference(resolution,[],[f80,f57])).
% 1.50/0.57  fof(f80,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f23])).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.50/0.57    inference(ennf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.50/0.57  fof(f284,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(forward_demodulation,[],[f274,f85])).
% 1.50/0.57  fof(f85,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.57    inference(equality_resolution,[],[f70])).
% 1.50/0.57  fof(f70,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f44])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.57    inference(flattening,[],[f43])).
% 1.50/0.57  fof(f43,plain,(
% 1.50/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.57    inference(nnf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.57  fof(f274,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f51,f272])).
% 1.50/0.57  fof(f272,plain,(
% 1.50/0.57    k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f255,f121])).
% 1.50/0.57  fof(f121,plain,(
% 1.50/0.57    r2_relset_1(sK1,sK2,sK3,sK3)),
% 1.50/0.57    inference(resolution,[],[f93,f51])).
% 1.50/0.57  fof(f93,plain,(
% 1.50/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.50/0.57    inference(duplicate_literal_removal,[],[f92])).
% 1.50/0.57  fof(f92,plain,(
% 1.50/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.57    inference(equality_resolution,[],[f82])).
% 1.50/0.57  fof(f82,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f48])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(nnf_transformation,[],[f25])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(flattening,[],[f24])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.50/0.57    inference(ennf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.50/0.57  fof(f255,plain,(
% 1.50/0.57    ~r2_relset_1(sK1,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 1.50/0.57    inference(superposition,[],[f56,f251])).
% 1.50/0.57  fof(f251,plain,(
% 1.50/0.57    sK3 = sK4 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f250,f214])).
% 1.50/0.57  fof(f214,plain,(
% 1.50/0.57    k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2 | sK3 = sK4),
% 1.50/0.57    inference(resolution,[],[f211,f55])).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f29,f28])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    ? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f15,plain,(
% 1.50/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.50/0.57    inference(flattening,[],[f14])).
% 1.50/0.57  fof(f14,plain,(
% 1.50/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.50/0.57    inference(ennf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.50/0.57    inference(negated_conjecture,[],[f12])).
% 1.50/0.57  fof(f12,conjecture,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.50/0.57  fof(f211,plain,(
% 1.50/0.57    r2_hidden(sK5(sK3,sK4),sK1) | sK3 = sK4 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f210,f147])).
% 1.50/0.57  fof(f147,plain,(
% 1.50/0.57    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 1.50/0.57    inference(superposition,[],[f144,f129])).
% 1.50/0.57  fof(f129,plain,(
% 1.50/0.57    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 1.50/0.57    inference(resolution,[],[f72,f54])).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f72,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.57  fof(f144,plain,(
% 1.50/0.57    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f142,f53])).
% 1.50/0.57  fof(f53,plain,(
% 1.50/0.57    v1_funct_2(sK4,sK1,sK2)),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f142,plain,(
% 1.50/0.57    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.50/0.57    inference(resolution,[],[f73,f116])).
% 1.50/0.57  fof(f116,plain,(
% 1.50/0.57    sP0(sK1,sK4,sK2)),
% 1.50/0.57    inference(resolution,[],[f77,f54])).
% 1.50/0.57  fof(f77,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f47])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(nnf_transformation,[],[f27])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(definition_folding,[],[f22,f26])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(flattening,[],[f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.57  fof(f73,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f46])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.50/0.57    inference(rectify,[],[f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.50/0.57    inference(nnf_transformation,[],[f26])).
% 1.50/0.57  fof(f210,plain,(
% 1.50/0.57    sK1 != k1_relat_1(sK4) | r2_hidden(sK5(sK3,sK4),sK1) | sK3 = sK4 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f209,f101])).
% 1.50/0.57  fof(f101,plain,(
% 1.50/0.57    v1_relat_1(sK4)),
% 1.50/0.57    inference(resolution,[],[f71,f54])).
% 1.50/0.57  fof(f71,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f19])).
% 1.50/0.57  fof(f19,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.57  fof(f209,plain,(
% 1.50/0.57    sK1 != k1_relat_1(sK4) | r2_hidden(sK5(sK3,sK4),sK1) | ~v1_relat_1(sK4) | sK3 = sK4 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(resolution,[],[f180,f52])).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    v1_funct_1(sK4)),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f180,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK3,X0),sK1) | ~v1_relat_1(X0) | sK3 = X0 | k1_xboole_0 = sK2) )),
% 1.50/0.57    inference(superposition,[],[f162,f145])).
% 1.50/0.57  fof(f145,plain,(
% 1.50/0.57    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.50/0.57    inference(superposition,[],[f143,f128])).
% 1.50/0.57  fof(f128,plain,(
% 1.50/0.57    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 1.50/0.57    inference(resolution,[],[f72,f51])).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f141,f50])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    v1_funct_2(sK3,sK1,sK2)),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f141,plain,(
% 1.50/0.57    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.50/0.57    inference(resolution,[],[f73,f115])).
% 1.50/0.57  fof(f115,plain,(
% 1.50/0.57    sP0(sK1,sK3,sK2)),
% 1.50/0.57    inference(resolution,[],[f77,f51])).
% 1.50/0.57  fof(f162,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(sK5(sK3,X0),k1_relat_1(sK3)) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f160,f100])).
% 1.50/0.57  fof(f100,plain,(
% 1.50/0.57    v1_relat_1(sK3)),
% 1.50/0.57    inference(resolution,[],[f71,f51])).
% 1.50/0.57  fof(f160,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(sK5(sK3,X0),k1_relat_1(sK3)) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0 | ~v1_relat_1(sK3)) )),
% 1.50/0.57    inference(resolution,[],[f58,f49])).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    v1_funct_1(sK3)),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f58,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(flattening,[],[f16])).
% 1.50/0.57  fof(f16,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.50/0.57  fof(f250,plain,(
% 1.50/0.57    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(subsumption_resolution,[],[f249,f145])).
% 1.50/0.57  fof(f249,plain,(
% 1.50/0.57    sK1 != k1_relat_1(sK3) | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(superposition,[],[f248,f147])).
% 1.50/0.57  fof(f248,plain,(
% 1.50/0.57    k1_relat_1(sK4) != k1_relat_1(sK3) | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4),
% 1.50/0.57    inference(subsumption_resolution,[],[f247,f101])).
% 1.50/0.57  fof(f247,plain,(
% 1.50/0.57    k1_relat_1(sK4) != k1_relat_1(sK3) | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | ~v1_relat_1(sK4) | sK3 = sK4),
% 1.50/0.57    inference(resolution,[],[f220,f52])).
% 1.50/0.57  fof(f220,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0)) | ~v1_relat_1(X0) | sK3 = X0) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f218,f100])).
% 1.50/0.57  fof(f218,plain,(
% 1.50/0.57    ( ! [X0] : (k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0)) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0 | ~v1_relat_1(sK3)) )),
% 1.50/0.57    inference(resolution,[],[f59,f49])).
% 1.50/0.57  fof(f59,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f32])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.50/0.57    inference(cnf_transformation,[],[f30])).
% 1.50/0.57  fof(f291,plain,(
% 1.50/0.57    ( ! [X4] : (r2_relset_1(X4,k1_xboole_0,sK3,sK3)) )),
% 1.50/0.57    inference(resolution,[],[f284,f123])).
% 1.50/0.57  fof(f123,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | r2_relset_1(X0,k1_xboole_0,X1,X1)) )),
% 1.50/0.57    inference(superposition,[],[f93,f85])).
% 1.50/0.57  fof(f395,plain,(
% 1.50/0.57    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f336,f387])).
% 1.50/0.57  fof(f387,plain,(
% 1.50/0.57    k1_xboole_0 = sK4),
% 1.50/0.57    inference(resolution,[],[f383,f109])).
% 1.50/0.57  fof(f383,plain,(
% 1.50/0.57    v1_xboole_0(sK4)),
% 1.50/0.57    inference(resolution,[],[f376,f61])).
% 1.50/0.57  fof(f376,plain,(
% 1.50/0.57    ( ! [X1] : (~r2_hidden(X1,sK4)) )),
% 1.50/0.57    inference(resolution,[],[f285,f112])).
% 1.50/0.57  fof(f285,plain,(
% 1.50/0.57    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(forward_demodulation,[],[f276,f85])).
% 1.50/0.57  fof(f276,plain,(
% 1.50/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f54,f272])).
% 1.50/0.57  fof(f336,plain,(
% 1.50/0.57    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4)),
% 1.50/0.57    inference(backward_demodulation,[],[f277,f301])).
% 1.50/0.57  fof(f277,plain,(
% 1.50/0.57    ~r2_relset_1(sK1,k1_xboole_0,sK3,sK4)),
% 1.50/0.57    inference(backward_demodulation,[],[f56,f272])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (9210)------------------------------
% 1.50/0.57  % (9210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (9210)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (9210)Memory used [KB]: 6524
% 1.50/0.57  % (9210)Time elapsed: 0.157 s
% 1.50/0.57  % (9210)------------------------------
% 1.50/0.57  % (9210)------------------------------
% 1.50/0.57  % (9202)Success in time 0.212 s
%------------------------------------------------------------------------------
