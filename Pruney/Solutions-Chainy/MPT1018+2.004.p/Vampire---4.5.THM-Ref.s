%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:35 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 366 expanded)
%              Number of leaves         :   18 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  411 (1943 expanded)
%              Number of equality atoms :  119 ( 634 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f111,f153,f171,f249])).

fof(f249,plain,
    ( ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f247,f40])).

fof(f40,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f247,plain,
    ( sK2 = sK3
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f246,f156])).

fof(f156,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f37,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f37,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f246,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | sK2 = sK3
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f229])).

fof(f229,plain,
    ( ! [X1] :
        ( k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | ~ r2_hidden(X1,k1_xboole_0)
        | sK3 = X1 )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f228,f157])).

fof(f157,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f38,f83])).

fof(f38,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f228,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3,k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0)
        | k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | sK3 = X1 )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f227,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f214,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f214,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f213,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f213,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f165,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f176,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f176,plain,
    ( sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f110,f83])).

fof(f110,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_6
  <=> sK1 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f165,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f114,f83])).

fof(f114,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f113,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f57,f69])).

fof(f69,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f227,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | sK3 = X1
        | ~ r2_hidden(sK3,k1_relat_1(k1_xboole_0)) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f226,f215])).

fof(f226,plain,
    ( ! [X1] :
        ( k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | sK3 = X1
        | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(sK3,k1_relat_1(k1_xboole_0)) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f225,f187])).

fof(f187,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f70,f177])).

fof(f70,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f225,plain,
    ( ! [X1] :
        ( k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | sK3 = X1
        | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(sK3,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f224,f184])).

fof(f184,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f33,f177])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f224,plain,
    ( ! [X1] :
        ( k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | sK3 = X1
        | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(sK3,k1_relat_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f212,f185])).

fof(f185,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f36,f177])).

fof(f36,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f212,plain,
    ( ! [X1] :
        ( k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1)
        | sK3 = X1
        | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(sK3,k1_relat_1(k1_xboole_0))
        | ~ v2_funct_1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(superposition,[],[f42,f186])).

fof(f186,plain,
    ( k1_funct_1(k1_xboole_0,sK2) = k1_funct_1(k1_xboole_0,sK3)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f39,f177])).

fof(f39,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f171,plain,
    ( ~ spl7_2
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f169,f41])).

fof(f169,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl7_2
    | spl7_5 ),
    inference(forward_demodulation,[],[f163,f61])).

fof(f163,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl7_2
    | spl7_5 ),
    inference(backward_demodulation,[],[f106,f83])).

fof(f106,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_5
  <=> r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f153,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f151,f40])).

fof(f151,plain,
    ( sK2 = sK3
    | spl7_1 ),
    inference(forward_demodulation,[],[f150,f125])).

fof(f125,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | spl7_1 ),
    inference(resolution,[],[f67,f79])).

fof(f79,plain,
    ( ~ sP6(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_1
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,(
    ! [X0] :
      ( sP6(X0,sK0)
      | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) ) ),
    inference(resolution,[],[f37,f63])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f63_D])).

fof(f63_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f150,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | spl7_1 ),
    inference(forward_demodulation,[],[f149,f39])).

fof(f149,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | spl7_1 ),
    inference(resolution,[],[f68,f79])).

fof(f68,plain,(
    ! [X0] :
      ( sP6(X0,sK0)
      | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) ) ),
    inference(resolution,[],[f38,f63])).

fof(f111,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f102,f108,f104])).

fof(f102,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) ),
    inference(resolution,[],[f72,f49])).

fof(f72,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f35,f50])).

fof(f84,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f75,f81,f77])).

fof(f75,plain,
    ( k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f74,f33])).

fof(f74,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f73,f34])).

fof(f34,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f71,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f35,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f58,f63_D])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:27:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.51  % (21542)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.51  % (21537)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (21540)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (21549)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.51  % (21541)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.52  % (21541)Refutation not found, incomplete strategy% (21541)------------------------------
% 0.23/0.52  % (21541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (21545)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (21541)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (21541)Memory used [KB]: 10618
% 0.23/0.52  % (21541)Time elapsed: 0.095 s
% 0.23/0.52  % (21541)------------------------------
% 0.23/0.52  % (21541)------------------------------
% 0.23/0.52  % (21553)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.52  % (21536)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (21555)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.52  % (21556)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.52  % (21558)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.52  % (21538)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.52  % (21536)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (21550)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.52  % (21548)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (21535)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  % (21547)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.53  % (21557)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.53  % (21548)Refutation not found, incomplete strategy% (21548)------------------------------
% 0.23/0.53  % (21548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (21548)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (21548)Memory used [KB]: 6140
% 0.23/0.53  % (21548)Time elapsed: 0.107 s
% 0.23/0.53  % (21548)------------------------------
% 0.23/0.53  % (21548)------------------------------
% 0.23/0.53  % (21535)Refutation not found, incomplete strategy% (21535)------------------------------
% 0.23/0.53  % (21535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (21535)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (21535)Memory used [KB]: 10490
% 0.23/0.53  % (21535)Time elapsed: 0.101 s
% 0.23/0.53  % (21535)------------------------------
% 0.23/0.53  % (21535)------------------------------
% 0.23/0.53  % (21539)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.53  % (21560)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.53  % (21546)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (21546)Refutation not found, incomplete strategy% (21546)------------------------------
% 0.23/0.53  % (21546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (21546)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (21546)Memory used [KB]: 10490
% 0.23/0.53  % (21546)Time elapsed: 0.118 s
% 0.23/0.53  % (21546)------------------------------
% 0.23/0.53  % (21546)------------------------------
% 0.23/0.54  % (21544)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.54  % (21554)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.54  % (21559)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.54  % (21551)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.54  % (21543)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.54  % (21552)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f250,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f84,f111,f153,f171,f249])).
% 1.38/0.55  fof(f249,plain,(
% 1.38/0.55    ~spl7_2 | ~spl7_6),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f248])).
% 1.38/0.55  fof(f248,plain,(
% 1.38/0.55    $false | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f247,f40])).
% 1.38/0.55  fof(f40,plain,(
% 1.38/0.55    sK2 != sK3),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22,f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f13,plain,(
% 1.38/0.55    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.38/0.55    inference(flattening,[],[f12])).
% 1.38/0.55  fof(f12,plain,(
% 1.38/0.55    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.38/0.55    inference(ennf_transformation,[],[f11])).
% 1.38/0.55  fof(f11,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.38/0.55    inference(negated_conjecture,[],[f10])).
% 1.38/0.55  fof(f10,conjecture,(
% 1.38/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 1.38/0.55  fof(f247,plain,(
% 1.38/0.55    sK2 = sK3 | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f246,f156])).
% 1.38/0.55  fof(f156,plain,(
% 1.38/0.55    r2_hidden(sK2,k1_xboole_0) | ~spl7_2),
% 1.38/0.55    inference(backward_demodulation,[],[f37,f83])).
% 1.38/0.55  fof(f83,plain,(
% 1.38/0.55    k1_xboole_0 = sK0 | ~spl7_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f81])).
% 1.38/0.55  fof(f81,plain,(
% 1.38/0.55    spl7_2 <=> k1_xboole_0 = sK0),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.38/0.55  fof(f37,plain,(
% 1.38/0.55    r2_hidden(sK2,sK0)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f246,plain,(
% 1.38/0.55    ~r2_hidden(sK2,k1_xboole_0) | sK2 = sK3 | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(equality_resolution,[],[f229])).
% 1.38/0.55  fof(f229,plain,(
% 1.38/0.55    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | ~r2_hidden(X1,k1_xboole_0) | sK3 = X1) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f228,f157])).
% 1.38/0.55  fof(f157,plain,(
% 1.38/0.55    r2_hidden(sK3,k1_xboole_0) | ~spl7_2),
% 1.38/0.55    inference(backward_demodulation,[],[f38,f83])).
% 1.38/0.55  fof(f38,plain,(
% 1.38/0.55    r2_hidden(sK3,sK0)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f228,plain,(
% 1.38/0.55    ( ! [X1] : (~r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | sK3 = X1) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(forward_demodulation,[],[f227,f215])).
% 1.38/0.55  fof(f215,plain,(
% 1.38/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f214,f41])).
% 1.38/0.55  fof(f41,plain,(
% 1.38/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.55  fof(f214,plain,(
% 1.38/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(resolution,[],[f213,f49])).
% 1.38/0.55  fof(f49,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(flattening,[],[f28])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(nnf_transformation,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.55  fof(f213,plain,(
% 1.38/0.55    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(forward_demodulation,[],[f165,f177])).
% 1.38/0.55  fof(f177,plain,(
% 1.38/0.55    k1_xboole_0 = sK1 | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(forward_demodulation,[],[f176,f61])).
% 1.38/0.55  fof(f61,plain,(
% 1.38/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.38/0.55    inference(equality_resolution,[],[f54])).
% 1.38/0.55  fof(f54,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f32])).
% 1.38/0.55  fof(f32,plain,(
% 1.38/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.38/0.55    inference(flattening,[],[f31])).
% 1.38/0.55  fof(f31,plain,(
% 1.38/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.38/0.55    inference(nnf_transformation,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.38/0.55  fof(f176,plain,(
% 1.38/0.55    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(forward_demodulation,[],[f110,f83])).
% 1.38/0.55  fof(f110,plain,(
% 1.38/0.55    sK1 = k2_zfmisc_1(sK0,sK0) | ~spl7_6),
% 1.38/0.55    inference(avatar_component_clause,[],[f108])).
% 1.38/0.55  fof(f108,plain,(
% 1.38/0.55    spl7_6 <=> sK1 = k2_zfmisc_1(sK0,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.38/0.55  fof(f165,plain,(
% 1.38/0.55    r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~spl7_2),
% 1.38/0.55    inference(backward_demodulation,[],[f114,f83])).
% 1.38/0.55  fof(f114,plain,(
% 1.38/0.55    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.38/0.55    inference(resolution,[],[f113,f50])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f30])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.38/0.55    inference(nnf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.55  fof(f113,plain,(
% 1.38/0.55    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.38/0.55    inference(subsumption_resolution,[],[f112,f35])).
% 1.38/0.55  fof(f35,plain,(
% 1.38/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f112,plain,(
% 1.38/0.55    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.55    inference(superposition,[],[f57,f69])).
% 1.38/0.55  fof(f69,plain,(
% 1.38/0.55    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.38/0.55    inference(resolution,[],[f35,f56])).
% 1.38/0.55  fof(f56,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f17])).
% 1.38/0.55  fof(f17,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f8])).
% 1.38/0.55  fof(f8,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f18])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.38/0.55  fof(f227,plain,(
% 1.38/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | sK3 = X1 | ~r2_hidden(sK3,k1_relat_1(k1_xboole_0))) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(forward_demodulation,[],[f226,f215])).
% 1.38/0.55  fof(f226,plain,(
% 1.38/0.55    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | sK3 = X1 | ~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK3,k1_relat_1(k1_xboole_0))) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f225,f187])).
% 1.38/0.55  fof(f187,plain,(
% 1.38/0.55    v1_relat_1(k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(backward_demodulation,[],[f70,f177])).
% 1.38/0.55  fof(f70,plain,(
% 1.38/0.55    v1_relat_1(sK1)),
% 1.38/0.55    inference(resolution,[],[f35,f55])).
% 1.38/0.55  fof(f55,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f16])).
% 1.38/0.55  fof(f16,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.55  fof(f225,plain,(
% 1.38/0.55    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | sK3 = X1 | ~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK3,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f224,f184])).
% 1.38/0.55  fof(f184,plain,(
% 1.38/0.55    v1_funct_1(k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(backward_demodulation,[],[f33,f177])).
% 1.38/0.55  fof(f33,plain,(
% 1.38/0.55    v1_funct_1(sK1)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f224,plain,(
% 1.38/0.55    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | sK3 = X1 | ~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK3,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f212,f185])).
% 1.38/0.55  fof(f185,plain,(
% 1.38/0.55    v2_funct_1(k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(backward_demodulation,[],[f36,f177])).
% 1.38/0.55  fof(f36,plain,(
% 1.38/0.55    v2_funct_1(sK1)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f212,plain,(
% 1.38/0.55    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK2) != k1_funct_1(k1_xboole_0,X1) | sK3 = X1 | ~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK3,k1_relat_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(superposition,[],[f42,f186])).
% 1.38/0.55  fof(f186,plain,(
% 1.38/0.55    k1_funct_1(k1_xboole_0,sK2) = k1_funct_1(k1_xboole_0,sK3) | (~spl7_2 | ~spl7_6)),
% 1.38/0.55    inference(backward_demodulation,[],[f39,f177])).
% 1.38/0.55  fof(f39,plain,(
% 1.38/0.55    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f27])).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.55    inference(rectify,[],[f24])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.55    inference(nnf_transformation,[],[f15])).
% 1.38/0.55  fof(f15,plain,(
% 1.38/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.55    inference(flattening,[],[f14])).
% 1.38/0.55  fof(f14,plain,(
% 1.38/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.38/0.55  fof(f171,plain,(
% 1.38/0.55    ~spl7_2 | spl7_5),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f170])).
% 1.38/0.55  fof(f170,plain,(
% 1.38/0.55    $false | (~spl7_2 | spl7_5)),
% 1.38/0.55    inference(subsumption_resolution,[],[f169,f41])).
% 1.38/0.55  fof(f169,plain,(
% 1.38/0.55    ~r1_tarski(k1_xboole_0,sK1) | (~spl7_2 | spl7_5)),
% 1.38/0.55    inference(forward_demodulation,[],[f163,f61])).
% 1.38/0.55  fof(f163,plain,(
% 1.38/0.55    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | (~spl7_2 | spl7_5)),
% 1.38/0.55    inference(backward_demodulation,[],[f106,f83])).
% 1.38/0.55  fof(f106,plain,(
% 1.38/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | spl7_5),
% 1.38/0.55    inference(avatar_component_clause,[],[f104])).
% 1.38/0.55  fof(f104,plain,(
% 1.38/0.55    spl7_5 <=> r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.38/0.55  fof(f153,plain,(
% 1.38/0.55    spl7_1),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f152])).
% 1.38/0.55  fof(f152,plain,(
% 1.38/0.55    $false | spl7_1),
% 1.38/0.55    inference(subsumption_resolution,[],[f151,f40])).
% 1.38/0.55  fof(f151,plain,(
% 1.38/0.55    sK2 = sK3 | spl7_1),
% 1.38/0.55    inference(forward_demodulation,[],[f150,f125])).
% 1.38/0.55  fof(f125,plain,(
% 1.38/0.55    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | spl7_1),
% 1.38/0.55    inference(resolution,[],[f67,f79])).
% 1.38/0.55  fof(f79,plain,(
% 1.38/0.55    ~sP6(sK1,sK0) | spl7_1),
% 1.38/0.55    inference(avatar_component_clause,[],[f77])).
% 1.38/0.55  fof(f77,plain,(
% 1.38/0.55    spl7_1 <=> sP6(sK1,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.38/0.55  fof(f67,plain,(
% 1.38/0.55    ( ! [X0] : (sP6(X0,sK0) | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))) )),
% 1.38/0.55    inference(resolution,[],[f37,f63])).
% 1.38/0.55  fof(f63,plain,(
% 1.38/0.55    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f63_D])).
% 1.38/0.55  fof(f63_D,plain,(
% 1.38/0.55    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 1.38/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.38/0.55  fof(f150,plain,(
% 1.38/0.55    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | spl7_1),
% 1.38/0.55    inference(forward_demodulation,[],[f149,f39])).
% 1.38/0.55  fof(f149,plain,(
% 1.38/0.55    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | spl7_1),
% 1.38/0.55    inference(resolution,[],[f68,f79])).
% 1.38/0.55  fof(f68,plain,(
% 1.38/0.55    ( ! [X0] : (sP6(X0,sK0) | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))) )),
% 1.38/0.55    inference(resolution,[],[f38,f63])).
% 1.38/0.55  fof(f111,plain,(
% 1.38/0.55    ~spl7_5 | spl7_6),
% 1.38/0.55    inference(avatar_split_clause,[],[f102,f108,f104])).
% 1.38/0.55  fof(f102,plain,(
% 1.38/0.55    sK1 = k2_zfmisc_1(sK0,sK0) | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)),
% 1.38/0.55    inference(resolution,[],[f72,f49])).
% 1.38/0.55  fof(f72,plain,(
% 1.38/0.55    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 1.38/0.55    inference(resolution,[],[f35,f50])).
% 1.38/0.55  fof(f84,plain,(
% 1.38/0.55    ~spl7_1 | spl7_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f75,f81,f77])).
% 1.38/0.55  fof(f75,plain,(
% 1.38/0.55    k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 1.38/0.55    inference(subsumption_resolution,[],[f74,f33])).
% 1.38/0.55  fof(f74,plain,(
% 1.38/0.55    k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 1.38/0.55    inference(subsumption_resolution,[],[f73,f34])).
% 1.38/0.55  fof(f34,plain,(
% 1.38/0.55    v1_funct_2(sK1,sK0,sK0)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f73,plain,(
% 1.38/0.55    k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 1.38/0.55    inference(subsumption_resolution,[],[f71,f36])).
% 1.38/0.55  fof(f71,plain,(
% 1.38/0.55    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 1.38/0.55    inference(resolution,[],[f35,f64])).
% 1.38/0.55  fof(f64,plain,(
% 1.38/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP6(X3,X0)) )),
% 1.38/0.55    inference(general_splitting,[],[f58,f63_D])).
% 1.38/0.55  fof(f58,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f20,plain,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.38/0.55    inference(flattening,[],[f19])).
% 1.38/0.55  fof(f19,plain,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.38/0.55    inference(ennf_transformation,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (21536)------------------------------
% 1.38/0.55  % (21536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (21536)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (21536)Memory used [KB]: 10746
% 1.38/0.55  % (21536)Time elapsed: 0.096 s
% 1.38/0.55  % (21536)------------------------------
% 1.38/0.55  % (21536)------------------------------
% 1.38/0.55  % (21534)Success in time 0.176 s
%------------------------------------------------------------------------------
