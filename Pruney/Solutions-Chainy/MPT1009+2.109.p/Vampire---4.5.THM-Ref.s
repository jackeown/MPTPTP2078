%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:41 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 612 expanded)
%              Number of leaves         :   21 ( 169 expanded)
%              Depth                    :   18
%              Number of atoms          :  279 (2078 expanded)
%              Number of equality atoms :   64 ( 376 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f527,f647])).

fof(f647,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f645,f227])).

fof(f227,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f215,f147])).

fof(f147,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f135,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f72,f60,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f215,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f135,f146,f203,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f203,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f135,f178,f71])).

fof(f178,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f146,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f146,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f135,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f645,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f637,f131])).

fof(f131,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f60,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f637,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1 ),
    inference(superposition,[],[f62,f551])).

fof(f551,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f135,f58,f545,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f545,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f173,f532,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f532,plain,
    ( r1_tarski(k1_tarski(sK0),k1_relat_1(sK3))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f530,f65])).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f530,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),k1_relat_1(sK3))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f363,f363,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f363,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f173,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f132,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f132,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f527,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f525,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f525,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f524,f482])).

fof(f482,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f63,f393,f84])).

fof(f393,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | spl4_1 ),
    inference(forward_demodulation,[],[f385,f382])).

fof(f382,plain,
    ( k1_xboole_0 = sK3
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f135,f374,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f374,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | spl4_1 ),
    inference(superposition,[],[f370,f347])).

fof(f347,plain,(
    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    inference(superposition,[],[f339,f136])).

fof(f136,plain,(
    ! [X0] : k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f135,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f339,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f147,f172])).

fof(f172,plain,(
    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f135,f132,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f370,plain,
    ( k1_xboole_0 = k11_relat_1(sK3,sK0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f135,f364,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f364,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f362])).

fof(f385,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0)
    | spl4_1 ),
    inference(superposition,[],[f227,f374])).

fof(f524,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f241,f382])).

fof(f241,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(unit_resulting_resolution,[],[f194,f86])).

fof(f194,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) ),
    inference(forward_demodulation,[],[f193,f131])).

fof(f193,plain,(
    ~ m1_subset_1(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) ),
    inference(unit_resulting_resolution,[],[f62,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6016)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (6032)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (6034)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (6024)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (6017)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (6028)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (6033)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (6027)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (6027)Refutation not found, incomplete strategy% (6027)------------------------------
% 0.21/0.52  % (6027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6027)Memory used [KB]: 1791
% 0.21/0.52  % (6027)Time elapsed: 0.112 s
% 0.21/0.52  % (6027)------------------------------
% 0.21/0.52  % (6027)------------------------------
% 0.21/0.52  % (6012)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (6009)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (6025)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (6036)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (6029)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (6011)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (6015)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (6019)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (6025)Refutation not found, incomplete strategy% (6025)------------------------------
% 0.21/0.53  % (6025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6013)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (6019)Refutation not found, incomplete strategy% (6019)------------------------------
% 0.21/0.53  % (6019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6019)Memory used [KB]: 10746
% 0.21/0.53  % (6019)Time elapsed: 0.124 s
% 0.21/0.53  % (6019)------------------------------
% 0.21/0.53  % (6019)------------------------------
% 0.21/0.53  % (6037)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (6021)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (6010)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.53  % (6020)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.53  % (6031)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (6025)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (6025)Memory used [KB]: 10618
% 1.27/0.53  % (6025)Time elapsed: 0.121 s
% 1.27/0.53  % (6025)------------------------------
% 1.27/0.53  % (6025)------------------------------
% 1.27/0.53  % (6035)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.54  % (6023)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.54  % (6026)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.54  % (6036)Refutation not found, incomplete strategy% (6036)------------------------------
% 1.27/0.54  % (6036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (6018)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.54  % (6038)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.54  % (6037)Refutation not found, incomplete strategy% (6037)------------------------------
% 1.27/0.54  % (6037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (6037)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (6037)Memory used [KB]: 10874
% 1.27/0.54  % (6037)Time elapsed: 0.132 s
% 1.27/0.54  % (6037)------------------------------
% 1.27/0.54  % (6037)------------------------------
% 1.27/0.54  % (6026)Refutation not found, incomplete strategy% (6026)------------------------------
% 1.27/0.54  % (6026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (6026)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (6026)Memory used [KB]: 1791
% 1.27/0.54  % (6026)Time elapsed: 0.096 s
% 1.27/0.54  % (6026)------------------------------
% 1.27/0.54  % (6026)------------------------------
% 1.27/0.54  % (6038)Refutation not found, incomplete strategy% (6038)------------------------------
% 1.27/0.54  % (6038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (6038)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (6038)Memory used [KB]: 1663
% 1.27/0.54  % (6038)Time elapsed: 0.141 s
% 1.27/0.54  % (6038)------------------------------
% 1.27/0.54  % (6038)------------------------------
% 1.27/0.54  % (6036)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (6036)Memory used [KB]: 6268
% 1.27/0.54  % (6036)Time elapsed: 0.132 s
% 1.27/0.54  % (6036)------------------------------
% 1.27/0.54  % (6036)------------------------------
% 1.27/0.54  % (6014)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.55  % (6030)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.55  % (6010)Refutation not found, incomplete strategy% (6010)------------------------------
% 1.39/0.55  % (6010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (6010)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (6010)Memory used [KB]: 1663
% 1.39/0.55  % (6010)Time elapsed: 0.111 s
% 1.39/0.55  % (6010)------------------------------
% 1.39/0.55  % (6010)------------------------------
% 1.39/0.56  % (6022)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.56  % (6023)Refutation not found, incomplete strategy% (6023)------------------------------
% 1.39/0.56  % (6023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (6023)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (6023)Memory used [KB]: 1918
% 1.39/0.56  % (6023)Time elapsed: 0.156 s
% 1.39/0.56  % (6023)------------------------------
% 1.39/0.56  % (6023)------------------------------
% 1.88/0.65  % (6066)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.88/0.65  % (6081)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.88/0.66  % (6068)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.88/0.66  % (6068)Refutation not found, incomplete strategy% (6068)------------------------------
% 1.88/0.66  % (6068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.66  % (6068)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.66  
% 1.88/0.66  % (6068)Memory used [KB]: 6268
% 1.88/0.66  % (6068)Time elapsed: 0.099 s
% 1.88/0.66  % (6068)------------------------------
% 1.88/0.66  % (6068)------------------------------
% 1.88/0.66  % (6063)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.88/0.66  % (6012)Refutation not found, incomplete strategy% (6012)------------------------------
% 1.88/0.66  % (6012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.67  % (6074)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.88/0.67  % (6076)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.88/0.67  % (6012)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.67  
% 1.88/0.67  % (6012)Memory used [KB]: 6268
% 1.88/0.67  % (6012)Time elapsed: 0.250 s
% 1.88/0.67  % (6012)------------------------------
% 1.88/0.67  % (6012)------------------------------
% 2.18/0.69  % (6076)Refutation not found, incomplete strategy% (6076)------------------------------
% 2.18/0.69  % (6076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (6084)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.18/0.70  % (6086)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.18/0.70  % (6088)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.18/0.71  % (6076)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.71  
% 2.18/0.71  % (6076)Memory used [KB]: 10874
% 2.18/0.71  % (6076)Time elapsed: 0.125 s
% 2.18/0.71  % (6076)------------------------------
% 2.18/0.71  % (6076)------------------------------
% 2.18/0.72  % (6074)Refutation found. Thanks to Tanya!
% 2.18/0.72  % SZS status Theorem for theBenchmark
% 2.18/0.72  % SZS output start Proof for theBenchmark
% 2.18/0.72  fof(f648,plain,(
% 2.18/0.72    $false),
% 2.18/0.72    inference(avatar_sat_refutation,[],[f527,f647])).
% 2.18/0.72  fof(f647,plain,(
% 2.18/0.72    ~spl4_1),
% 2.18/0.72    inference(avatar_contradiction_clause,[],[f646])).
% 2.18/0.72  fof(f646,plain,(
% 2.18/0.72    $false | ~spl4_1),
% 2.18/0.72    inference(subsumption_resolution,[],[f645,f227])).
% 2.18/0.72  fof(f227,plain,(
% 2.18/0.72    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 2.18/0.72    inference(forward_demodulation,[],[f215,f147])).
% 2.18/0.72  fof(f147,plain,(
% 2.18/0.72    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f75])).
% 2.18/0.72  fof(f75,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f38])).
% 2.18/0.72  fof(f38,plain,(
% 2.18/0.72    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(ennf_transformation,[],[f18])).
% 2.18/0.72  fof(f18,axiom,(
% 2.18/0.72    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.18/0.72  fof(f135,plain,(
% 2.18/0.72    v1_relat_1(sK3)),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f72,f60,f71])).
% 2.18/0.72  fof(f71,plain,(
% 2.18/0.72    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f36])).
% 2.18/0.72  fof(f36,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f14])).
% 2.18/0.72  fof(f14,axiom,(
% 2.18/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.18/0.72  fof(f60,plain,(
% 2.18/0.72    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.18/0.72    inference(cnf_transformation,[],[f50])).
% 2.18/0.72  fof(f50,plain,(
% 2.18/0.72    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 2.18/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f49])).
% 2.18/0.72  fof(f49,plain,(
% 2.18/0.72    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 2.18/0.72    introduced(choice_axiom,[])).
% 2.18/0.72  fof(f30,plain,(
% 2.18/0.72    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.18/0.72    inference(flattening,[],[f29])).
% 2.18/0.72  fof(f29,plain,(
% 2.18/0.72    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.18/0.72    inference(ennf_transformation,[],[f28])).
% 2.18/0.72  fof(f28,negated_conjecture,(
% 2.18/0.72    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.18/0.72    inference(negated_conjecture,[],[f27])).
% 2.18/0.72  fof(f27,conjecture,(
% 2.18/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 2.18/0.72  fof(f72,plain,(
% 2.18/0.72    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f17])).
% 2.18/0.72  fof(f17,axiom,(
% 2.18/0.72    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.18/0.72  fof(f215,plain,(
% 2.18/0.72    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(sK3))) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f146,f203,f70])).
% 2.18/0.72  fof(f70,plain,(
% 2.18/0.72    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f35])).
% 2.18/0.72  fof(f35,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.18/0.72    inference(flattening,[],[f34])).
% 2.18/0.72  fof(f34,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f21])).
% 2.18/0.72  fof(f21,axiom,(
% 2.18/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.18/0.72  fof(f203,plain,(
% 2.18/0.72    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f178,f71])).
% 2.18/0.72  fof(f178,plain,(
% 2.18/0.72    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f146,f86])).
% 2.18/0.72  fof(f86,plain,(
% 2.18/0.72    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f55])).
% 2.18/0.72  fof(f55,plain,(
% 2.18/0.72    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/0.72    inference(nnf_transformation,[],[f12])).
% 2.18/0.72  fof(f12,axiom,(
% 2.18/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.72  fof(f146,plain,(
% 2.18/0.72    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f74])).
% 2.18/0.72  fof(f74,plain,(
% 2.18/0.72    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f37])).
% 2.18/0.72  fof(f37,plain,(
% 2.18/0.72    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(ennf_transformation,[],[f23])).
% 2.18/0.72  fof(f23,axiom,(
% 2.18/0.72    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 2.18/0.72  fof(f645,plain,(
% 2.18/0.72    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_1),
% 2.18/0.72    inference(forward_demodulation,[],[f637,f131])).
% 2.18/0.72  fof(f131,plain,(
% 2.18/0.72    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f60,f95])).
% 2.18/0.72  fof(f95,plain,(
% 2.18/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f48])).
% 2.18/0.72  fof(f48,plain,(
% 2.18/0.72    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.72    inference(ennf_transformation,[],[f26])).
% 2.18/0.72  fof(f26,axiom,(
% 2.18/0.72    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.18/0.72  fof(f637,plain,(
% 2.18/0.72    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | ~spl4_1),
% 2.18/0.72    inference(superposition,[],[f62,f551])).
% 2.18/0.72  fof(f551,plain,(
% 2.18/0.72    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_1),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f58,f545,f80])).
% 2.18/0.72  fof(f80,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f42])).
% 2.18/0.72  fof(f42,plain,(
% 2.18/0.72    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(flattening,[],[f41])).
% 2.18/0.72  fof(f41,plain,(
% 2.18/0.72    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.18/0.72    inference(ennf_transformation,[],[f24])).
% 2.18/0.72  fof(f24,axiom,(
% 2.18/0.72    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 2.18/0.72  fof(f545,plain,(
% 2.18/0.72    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_1),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f173,f532,f84])).
% 2.18/0.72  fof(f84,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.18/0.72    inference(cnf_transformation,[],[f54])).
% 2.18/0.72  fof(f54,plain,(
% 2.18/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.72    inference(flattening,[],[f53])).
% 2.18/0.72  fof(f53,plain,(
% 2.18/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.72    inference(nnf_transformation,[],[f1])).
% 2.18/0.72  fof(f1,axiom,(
% 2.18/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.18/0.72  fof(f532,plain,(
% 2.18/0.72    r1_tarski(k1_tarski(sK0),k1_relat_1(sK3)) | ~spl4_1),
% 2.18/0.72    inference(forward_demodulation,[],[f530,f65])).
% 2.18/0.72  fof(f65,plain,(
% 2.18/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f3])).
% 2.18/0.72  fof(f3,axiom,(
% 2.18/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.18/0.72  fof(f530,plain,(
% 2.18/0.72    r1_tarski(k2_tarski(sK0,sK0),k1_relat_1(sK3)) | ~spl4_1),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f363,f363,f93])).
% 2.18/0.72  fof(f93,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f57])).
% 2.18/0.72  fof(f57,plain,(
% 2.18/0.72    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.18/0.72    inference(flattening,[],[f56])).
% 2.18/0.72  fof(f56,plain,(
% 2.18/0.72    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.18/0.72    inference(nnf_transformation,[],[f10])).
% 2.18/0.72  fof(f10,axiom,(
% 2.18/0.72    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.18/0.72  fof(f363,plain,(
% 2.18/0.72    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl4_1),
% 2.18/0.72    inference(avatar_component_clause,[],[f362])).
% 2.18/0.72  fof(f362,plain,(
% 2.18/0.72    spl4_1 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 2.18/0.72    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.18/0.72  fof(f173,plain,(
% 2.18/0.72    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f132,f76])).
% 2.18/0.72  fof(f76,plain,(
% 2.18/0.72    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f51])).
% 2.18/0.72  fof(f51,plain,(
% 2.18/0.72    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(nnf_transformation,[],[f39])).
% 2.18/0.72  fof(f39,plain,(
% 2.18/0.72    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(ennf_transformation,[],[f16])).
% 2.18/0.72  fof(f16,axiom,(
% 2.18/0.72    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.18/0.72  fof(f132,plain,(
% 2.18/0.72    v4_relat_1(sK3,k1_tarski(sK0))),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f60,f88])).
% 2.18/0.72  fof(f88,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f45])).
% 2.18/0.72  fof(f45,plain,(
% 2.18/0.72    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.72    inference(ennf_transformation,[],[f25])).
% 2.18/0.72  fof(f25,axiom,(
% 2.18/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.18/0.72  fof(f58,plain,(
% 2.18/0.72    v1_funct_1(sK3)),
% 2.18/0.72    inference(cnf_transformation,[],[f50])).
% 2.18/0.72  fof(f62,plain,(
% 2.18/0.72    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.18/0.72    inference(cnf_transformation,[],[f50])).
% 2.18/0.72  fof(f527,plain,(
% 2.18/0.72    spl4_1),
% 2.18/0.72    inference(avatar_contradiction_clause,[],[f526])).
% 2.18/0.72  fof(f526,plain,(
% 2.18/0.72    $false | spl4_1),
% 2.18/0.72    inference(subsumption_resolution,[],[f525,f63])).
% 2.18/0.72  fof(f63,plain,(
% 2.18/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f2])).
% 2.18/0.72  fof(f2,axiom,(
% 2.18/0.72    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.18/0.72  fof(f525,plain,(
% 2.18/0.72    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_1),
% 2.18/0.72    inference(forward_demodulation,[],[f524,f482])).
% 2.18/0.72  fof(f482,plain,(
% 2.18/0.72    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | spl4_1),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f63,f393,f84])).
% 2.18/0.72  fof(f393,plain,(
% 2.18/0.72    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | spl4_1),
% 2.18/0.72    inference(forward_demodulation,[],[f385,f382])).
% 2.18/0.72  fof(f382,plain,(
% 2.18/0.72    k1_xboole_0 = sK3 | spl4_1),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f374,f67])).
% 2.18/0.72  fof(f67,plain,(
% 2.18/0.72    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f32])).
% 2.18/0.72  fof(f32,plain,(
% 2.18/0.72    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.18/0.72    inference(flattening,[],[f31])).
% 2.18/0.72  fof(f31,plain,(
% 2.18/0.72    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f22])).
% 2.18/0.72  fof(f22,axiom,(
% 2.18/0.72    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 2.18/0.72  fof(f374,plain,(
% 2.18/0.72    k1_xboole_0 = k2_relat_1(sK3) | spl4_1),
% 2.18/0.72    inference(superposition,[],[f370,f347])).
% 2.18/0.72  fof(f347,plain,(
% 2.18/0.72    k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 2.18/0.72    inference(superposition,[],[f339,f136])).
% 2.18/0.72  fof(f136,plain,(
% 2.18/0.72    ( ! [X0] : (k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0))) )),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f68])).
% 2.18/0.72  fof(f68,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f33])).
% 2.18/0.72  fof(f33,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f15])).
% 2.18/0.72  fof(f15,axiom,(
% 2.18/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 2.18/0.72  fof(f339,plain,(
% 2.18/0.72    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))),
% 2.18/0.72    inference(superposition,[],[f147,f172])).
% 2.18/0.72  fof(f172,plain,(
% 2.18/0.72    sK3 = k7_relat_1(sK3,k1_tarski(sK0))),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f132,f81])).
% 2.18/0.72  fof(f81,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f44])).
% 2.18/0.72  fof(f44,plain,(
% 2.18/0.72    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(flattening,[],[f43])).
% 2.18/0.72  fof(f43,plain,(
% 2.18/0.72    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/0.72    inference(ennf_transformation,[],[f20])).
% 2.18/0.72  fof(f20,axiom,(
% 2.18/0.72    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.18/0.72  fof(f370,plain,(
% 2.18/0.72    k1_xboole_0 = k11_relat_1(sK3,sK0) | spl4_1),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f135,f364,f79])).
% 2.18/0.72  fof(f79,plain,(
% 2.18/0.72    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f52])).
% 2.18/0.72  fof(f52,plain,(
% 2.18/0.72    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(nnf_transformation,[],[f40])).
% 2.18/0.72  fof(f40,plain,(
% 2.18/0.72    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.18/0.72    inference(ennf_transformation,[],[f19])).
% 2.18/0.72  fof(f19,axiom,(
% 2.18/0.72    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.18/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 2.18/0.72  fof(f364,plain,(
% 2.18/0.72    ~r2_hidden(sK0,k1_relat_1(sK3)) | spl4_1),
% 2.18/0.72    inference(avatar_component_clause,[],[f362])).
% 2.18/0.72  fof(f385,plain,(
% 2.18/0.72    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0)) ) | spl4_1),
% 2.18/0.72    inference(superposition,[],[f227,f374])).
% 2.18/0.72  fof(f524,plain,(
% 2.18/0.72    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_1),
% 2.18/0.72    inference(superposition,[],[f241,f382])).
% 2.18/0.72  fof(f241,plain,(
% 2.18/0.72    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f194,f86])).
% 2.18/0.72  fof(f194,plain,(
% 2.18/0.72    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))),
% 2.18/0.72    inference(forward_demodulation,[],[f193,f131])).
% 2.18/0.72  fof(f193,plain,(
% 2.18/0.72    ~m1_subset_1(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))),
% 2.18/0.72    inference(unit_resulting_resolution,[],[f62,f85])).
% 2.18/0.72  fof(f85,plain,(
% 2.18/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f55])).
% 2.18/0.72  % SZS output end Proof for theBenchmark
% 2.18/0.72  % (6074)------------------------------
% 2.18/0.72  % (6074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.72  % (6074)Termination reason: Refutation
% 2.18/0.72  
% 2.18/0.72  % (6074)Memory used [KB]: 11001
% 2.18/0.72  % (6074)Time elapsed: 0.156 s
% 2.18/0.72  % (6074)------------------------------
% 2.18/0.72  % (6074)------------------------------
% 2.18/0.73  % (6008)Success in time 0.351 s
%------------------------------------------------------------------------------
