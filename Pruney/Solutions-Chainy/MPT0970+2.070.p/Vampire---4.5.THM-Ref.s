%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:58 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 227 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 (1039 expanded)
%              Number of equality atoms :   68 ( 308 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f279,f336,f380])).

fof(f380,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f378,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f378,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f346,f369])).

fof(f369,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f368,f113])).

fof(f113,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f112,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f111,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f79,f70])).

fof(f70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f79,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ v4_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f63,f68])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f368,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f355,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f355,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f343,f68])).

fof(f343,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f73,f278])).

fof(f278,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f73,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f346,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f144,f278])).

fof(f144,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f143,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f43,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f336,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f334,f320])).

fof(f320,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f319,f144])).

fof(f319,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f313,f51])).

fof(f313,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_7 ),
    inference(resolution,[],[f296,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f296,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(X3,k2_relat_1(sK2)),sK1)
        | r1_tarski(X3,k2_relat_1(sK2)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f293,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f293,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f292,f40])).

fof(f292,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl5_7 ),
    inference(superposition,[],[f274,f61])).

fof(f274,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl5_7
  <=> ! [X0] :
        ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f334,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f331,f55])).

fof(f331,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f178,f40])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f62,f61])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f279,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f271,f276,f273])).

fof(f271,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f270,f41])).

fof(f41,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f270,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(sK3(X0),sK0)
      | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f266,f39])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f266,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(sK3(X0),sK0)
      | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f237,f40])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f211,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f65,f42])).

fof(f42,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (28071)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (28094)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (28089)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (28081)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (28072)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (28086)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (28073)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (28078)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (28079)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (28066)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (28088)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (28069)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28068)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28067)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28080)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (28070)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28074)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (28087)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (28087)Refutation not found, incomplete strategy% (28087)------------------------------
% 0.21/0.54  % (28087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28087)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28087)Memory used [KB]: 1791
% 0.21/0.54  % (28087)Time elapsed: 0.143 s
% 0.21/0.54  % (28087)------------------------------
% 0.21/0.54  % (28087)------------------------------
% 0.21/0.54  % (28092)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (28090)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (28095)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (28093)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (28084)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (28082)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (28091)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (28083)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (28077)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (28076)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (28075)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.62/0.57  % (28093)Refutation found. Thanks to Tanya!
% 1.62/0.57  % SZS status Theorem for theBenchmark
% 1.62/0.57  % SZS output start Proof for theBenchmark
% 1.62/0.57  fof(f381,plain,(
% 1.62/0.57    $false),
% 1.62/0.57    inference(avatar_sat_refutation,[],[f279,f336,f380])).
% 1.62/0.57  fof(f380,plain,(
% 1.62/0.57    ~spl5_8),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f379])).
% 1.62/0.57  fof(f379,plain,(
% 1.62/0.57    $false | ~spl5_8),
% 1.62/0.57    inference(subsumption_resolution,[],[f378,f45])).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.62/0.57    inference(cnf_transformation,[],[f7])).
% 1.62/0.57  fof(f7,axiom,(
% 1.62/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.62/0.57  fof(f378,plain,(
% 1.62/0.57    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~spl5_8),
% 1.62/0.57    inference(forward_demodulation,[],[f346,f369])).
% 1.62/0.57  fof(f369,plain,(
% 1.62/0.57    k1_xboole_0 = sK2 | ~spl5_8),
% 1.62/0.57    inference(subsumption_resolution,[],[f368,f113])).
% 1.62/0.57  fof(f113,plain,(
% 1.62/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f112,f66])).
% 1.62/0.57  fof(f66,plain,(
% 1.62/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.62/0.57    inference(equality_resolution,[],[f50])).
% 1.62/0.57  fof(f50,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.62/0.57    inference(cnf_transformation,[],[f30])).
% 1.62/0.57  fof(f30,plain,(
% 1.62/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.57    inference(flattening,[],[f29])).
% 1.62/0.57  fof(f29,plain,(
% 1.62/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.57    inference(nnf_transformation,[],[f2])).
% 1.62/0.57  fof(f2,axiom,(
% 1.62/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.57  fof(f112,plain,(
% 1.62/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.57    inference(resolution,[],[f111,f80])).
% 1.62/0.57  fof(f80,plain,(
% 1.62/0.57    ( ! [X0] : (~v4_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f79,f70])).
% 1.62/0.57  fof(f70,plain,(
% 1.62/0.57    v1_relat_1(k1_xboole_0)),
% 1.62/0.57    inference(superposition,[],[f46,f68])).
% 1.62/0.57  fof(f68,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.62/0.57    inference(equality_resolution,[],[f59])).
% 1.62/0.57  fof(f59,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.62/0.57    inference(cnf_transformation,[],[f37])).
% 1.62/0.57  fof(f37,plain,(
% 1.62/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.62/0.57    inference(flattening,[],[f36])).
% 1.62/0.57  fof(f36,plain,(
% 1.62/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.62/0.57    inference(nnf_transformation,[],[f3])).
% 1.62/0.57  fof(f3,axiom,(
% 1.62/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.62/0.57  fof(f46,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f6])).
% 1.62/0.57  fof(f6,axiom,(
% 1.62/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.62/0.57  fof(f79,plain,(
% 1.62/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.62/0.57    inference(superposition,[],[f47,f44])).
% 1.62/0.57  fof(f44,plain,(
% 1.62/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.57    inference(cnf_transformation,[],[f7])).
% 1.62/0.57  fof(f47,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f28])).
% 1.62/0.57  fof(f28,plain,(
% 1.62/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(nnf_transformation,[],[f17])).
% 1.62/0.57  fof(f17,plain,(
% 1.62/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f5])).
% 1.62/0.57  fof(f5,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.62/0.57  fof(f111,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v4_relat_1(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.62/0.57    inference(resolution,[],[f109,f56])).
% 1.62/0.57  fof(f56,plain,(
% 1.62/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f35,plain,(
% 1.62/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.62/0.57    inference(nnf_transformation,[],[f4])).
% 1.62/0.57  fof(f4,axiom,(
% 1.62/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.57  fof(f109,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 1.62/0.57    inference(superposition,[],[f63,f68])).
% 1.62/0.57  fof(f63,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f22])).
% 1.62/0.57  fof(f22,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f9])).
% 1.62/0.57  fof(f9,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.62/0.57  fof(f368,plain,(
% 1.62/0.57    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl5_8),
% 1.62/0.57    inference(resolution,[],[f355,f51])).
% 1.62/0.57  fof(f51,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f30])).
% 1.62/0.57  fof(f355,plain,(
% 1.62/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl5_8),
% 1.62/0.57    inference(forward_demodulation,[],[f343,f68])).
% 1.62/0.57  fof(f343,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl5_8),
% 1.62/0.57    inference(backward_demodulation,[],[f73,f278])).
% 1.62/0.57  fof(f278,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | ~spl5_8),
% 1.62/0.57    inference(avatar_component_clause,[],[f276])).
% 1.62/0.57  fof(f276,plain,(
% 1.62/0.57    spl5_8 <=> k1_xboole_0 = sK1),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.62/0.57  fof(f73,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.62/0.57    inference(resolution,[],[f55,f40])).
% 1.62/0.57  fof(f40,plain,(
% 1.62/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f27,plain,(
% 1.62/0.57    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26,f25])).
% 1.62/0.57  fof(f25,plain,(
% 1.62/0.57    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f26,plain,(
% 1.62/0.57    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f16,plain,(
% 1.62/0.57    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.62/0.57    inference(flattening,[],[f15])).
% 1.62/0.57  fof(f15,plain,(
% 1.62/0.57    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.62/0.57    inference(ennf_transformation,[],[f14])).
% 1.62/0.57  fof(f14,negated_conjecture,(
% 1.62/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.62/0.57    inference(negated_conjecture,[],[f13])).
% 1.62/0.57  fof(f13,conjecture,(
% 1.62/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.62/0.57  fof(f55,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f346,plain,(
% 1.62/0.57    k1_xboole_0 != k2_relat_1(sK2) | ~spl5_8),
% 1.62/0.57    inference(backward_demodulation,[],[f144,f278])).
% 1.62/0.57  fof(f144,plain,(
% 1.62/0.57    sK1 != k2_relat_1(sK2)),
% 1.62/0.57    inference(subsumption_resolution,[],[f143,f40])).
% 1.62/0.57  fof(f143,plain,(
% 1.62/0.57    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(superposition,[],[f43,f61])).
% 1.62/0.57  fof(f61,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f20])).
% 1.62/0.57  fof(f20,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f11])).
% 1.62/0.57  fof(f11,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.62/0.57  fof(f43,plain,(
% 1.62/0.57    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f336,plain,(
% 1.62/0.57    ~spl5_7),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f335])).
% 1.62/0.57  fof(f335,plain,(
% 1.62/0.57    $false | ~spl5_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f334,f320])).
% 1.62/0.57  fof(f320,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),sK1) | ~spl5_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f319,f144])).
% 1.62/0.57  fof(f319,plain,(
% 1.62/0.57    sK1 = k2_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~spl5_7),
% 1.62/0.57    inference(resolution,[],[f313,f51])).
% 1.62/0.57  fof(f313,plain,(
% 1.62/0.57    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_7),
% 1.62/0.57    inference(duplicate_literal_removal,[],[f311])).
% 1.62/0.57  fof(f311,plain,(
% 1.62/0.57    r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_7),
% 1.62/0.57    inference(resolution,[],[f296,f53])).
% 1.62/0.57  fof(f53,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f34])).
% 1.62/0.57  fof(f34,plain,(
% 1.62/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.62/0.57  fof(f33,plain,(
% 1.62/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f32,plain,(
% 1.62/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.57    inference(rectify,[],[f31])).
% 1.62/0.57  fof(f31,plain,(
% 1.62/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.57    inference(nnf_transformation,[],[f18])).
% 1.62/0.57  fof(f18,plain,(
% 1.62/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f1])).
% 1.62/0.57  fof(f1,axiom,(
% 1.62/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.57  fof(f296,plain,(
% 1.62/0.57    ( ! [X3] : (~r2_hidden(sK4(X3,k2_relat_1(sK2)),sK1) | r1_tarski(X3,k2_relat_1(sK2))) ) | ~spl5_7),
% 1.62/0.57    inference(resolution,[],[f293,f54])).
% 1.62/0.57  fof(f54,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f34])).
% 1.62/0.57  fof(f293,plain,(
% 1.62/0.57    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1)) ) | ~spl5_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f292,f40])).
% 1.62/0.57  fof(f292,plain,(
% 1.62/0.57    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl5_7),
% 1.62/0.57    inference(superposition,[],[f274,f61])).
% 1.62/0.57  fof(f274,plain,(
% 1.62/0.57    ( ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1)) ) | ~spl5_7),
% 1.62/0.57    inference(avatar_component_clause,[],[f273])).
% 1.62/0.57  fof(f273,plain,(
% 1.62/0.57    spl5_7 <=> ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.62/0.57  fof(f334,plain,(
% 1.62/0.57    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.62/0.57    inference(resolution,[],[f331,f55])).
% 1.62/0.57  fof(f331,plain,(
% 1.62/0.57    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.62/0.57    inference(resolution,[],[f178,f40])).
% 1.62/0.57  fof(f178,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 1.62/0.57    inference(duplicate_literal_removal,[],[f177])).
% 1.62/0.57  fof(f177,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(superposition,[],[f62,f61])).
% 1.62/0.57  fof(f62,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f21])).
% 1.62/0.57  fof(f21,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f10])).
% 1.62/0.57  fof(f10,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.62/0.57  fof(f279,plain,(
% 1.62/0.57    spl5_7 | spl5_8),
% 1.62/0.57    inference(avatar_split_clause,[],[f271,f276,f273])).
% 1.62/0.57  fof(f271,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = sK1 | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f270,f41])).
% 1.62/0.57  fof(f41,plain,(
% 1.62/0.57    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f270,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f266,f39])).
% 1.62/0.57  fof(f39,plain,(
% 1.62/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f266,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~r2_hidden(X0,sK1)) )),
% 1.62/0.57    inference(resolution,[],[f237,f40])).
% 1.62/0.57  fof(f237,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~v1_funct_2(sK2,X1,X2) | ~r2_hidden(X0,sK1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f211,f38])).
% 1.62/0.57  fof(f38,plain,(
% 1.62/0.57    v1_funct_1(sK2)),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f211,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | k1_xboole_0 = X2 | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~v1_funct_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 1.62/0.57    inference(superposition,[],[f65,f42])).
% 1.62/0.57  fof(f42,plain,(
% 1.62/0.57    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f65,plain,(
% 1.62/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f24])).
% 1.62/0.57  fof(f24,plain,(
% 1.62/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.62/0.57    inference(flattening,[],[f23])).
% 1.62/0.57  fof(f23,plain,(
% 1.62/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.62/0.57    inference(ennf_transformation,[],[f12])).
% 1.62/0.57  fof(f12,axiom,(
% 1.62/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (28093)------------------------------
% 1.62/0.57  % (28093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (28093)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (28093)Memory used [KB]: 6396
% 1.62/0.57  % (28093)Time elapsed: 0.172 s
% 1.62/0.57  % (28093)------------------------------
% 1.62/0.57  % (28093)------------------------------
% 1.62/0.58  % (28065)Success in time 0.215 s
%------------------------------------------------------------------------------
