%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t36_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 16.15s
% Output     : Refutation 16.15s
% Verified   : 
% Statistics : Number of formulae       :  174 (1972 expanded)
%              Number of leaves         :   22 ( 504 expanded)
%              Depth                    :   34
%              Number of atoms          :  481 (9134 expanded)
%              Number of equality atoms :   42 ( 309 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8745,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7278,f7018])).

fof(f7018,plain,(
    ! [X21,X20] : r2_relset_1(X20,X21,sK5,sK5) ),
    inference(backward_demodulation,[],[f6978,f3373])).

fof(f3373,plain,(
    ! [X21,X20] : r2_relset_1(X20,X21,k8_relat_1(o_0_0_xboole_0,sK5),k8_relat_1(o_0_0_xboole_0,sK5)) ),
    inference(superposition,[],[f213,f3220])).

fof(f3220,plain,(
    ! [X56,X55] : k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(o_0_0_xboole_0,sK8(k1_zfmisc_1(k2_zfmisc_1(X55,X56)))) ),
    inference(resolution,[],[f3201,f127])).

fof(f127,plain,(
    ! [X0,X1] : v1_relat_1(sK8(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f102,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f14,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',existence_m1_subset_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',cc1_relset_1)).

fof(f3201,plain,(
    ! [X68] :
      ( ~ v1_relat_1(X68)
      | k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(o_0_0_xboole_0,X68) ) ),
    inference(resolution,[],[f3187,f128])).

fof(f128,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f102,f76])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f58])).

fof(f58,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t36_relset_1)).

fof(f3187,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | k8_relat_1(o_0_0_xboole_0,X8) = k8_relat_1(o_0_0_xboole_0,X9)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f3185,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',dt_k8_relat_1)).

fof(f3185,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | k8_relat_1(o_0_0_xboole_0,X8) = k8_relat_1(o_0_0_xboole_0,X9)
      | ~ v1_relat_1(k8_relat_1(o_0_0_xboole_0,X8))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f3179,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k8_relat_1(X1,X0) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f88,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X0,X1)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f35,f56,f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> ( r2_hidden(k4_tarski(X3,X4),X1)
            & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ( k8_relat_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',d12_relat_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k8_relat_1(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ( ( k8_relat_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k8_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f3179,plain,(
    ! [X0,X1] :
      ( sP0(X1,o_0_0_xboole_0,k8_relat_1(o_0_0_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f3168,f79])).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',dt_o_0_0_xboole_0)).

fof(f3168,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_xboole_0(X10)
      | ~ v1_relat_1(X11)
      | sP0(X9,X10,k8_relat_1(o_0_0_xboole_0,X11)) ) ),
    inference(resolution,[],[f2971,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t7_boole)).

fof(f2971,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X1,X2,k8_relat_1(o_0_0_xboole_0,X0)),X2)
      | sP0(X1,X2,k8_relat_1(o_0_0_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2967,f797])).

fof(f797,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),o_0_0_xboole_0)
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f788,f89])).

fof(f89,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | r2_hidden(X6,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X1)
            | ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X0)
              & r2_hidden(sK10(X0,X1,X2),X1) )
            | r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(X6,X1) )
            & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                & r2_hidden(X6,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X4,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X0)
            & r2_hidden(sK10(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X4,X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(X6,X1) )
            & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                & r2_hidden(X6,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f788,plain,(
    ! [X5] : sP0(o_0_0_xboole_0,X5,o_0_0_xboole_0) ),
    inference(resolution,[],[f776,f143])).

fof(f143,plain,(
    m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(superposition,[],[f85,f139])).

fof(f139,plain,(
    o_0_0_xboole_0 = sK8(k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f136,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f120,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t6_boole)).

fof(f120,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f80,f79])).

fof(f136,plain,(
    v1_xboole_0(sK8(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f134,f85])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0)))
      | v1_xboole_0(sK8(k1_zfmisc_1(o_0_0_xboole_0))) ) ),
    inference(resolution,[],[f133,f85])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f131,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t2_subset)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) ) ),
    inference(resolution,[],[f104,f79])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t5_subset)).

fof(f776,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(o_0_0_xboole_0))
      | sP0(X43,X44,X43) ) ),
    inference(resolution,[],[f756,f131])).

fof(f756,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X0),sK10(X0,X1,X0)),X0)
      | sP0(X0,X1,X0) ) ),
    inference(factoring,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f2967,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | sP0(X1,X2,k8_relat_1(o_0_0_xboole_0,X0))
      | r2_hidden(k4_tarski(sK9(X1,X2,k8_relat_1(o_0_0_xboole_0,X0)),sK10(X1,X2,k8_relat_1(o_0_0_xboole_0,X0))),o_0_0_xboole_0)
      | r2_hidden(sK10(X1,X2,k8_relat_1(o_0_0_xboole_0,X0)),X2) ) ),
    inference(resolution,[],[f2963,f364])).

fof(f364,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( ~ sP0(X20,X21,X19)
      | sP0(X17,X18,X19)
      | r2_hidden(k4_tarski(sK9(X17,X18,X19),sK10(X17,X18,X19)),X20)
      | r2_hidden(sK10(X17,X18,X19),X18) ) ),
    inference(resolution,[],[f92,f90])).

fof(f90,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X2)
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2)
      | r2_hidden(sK10(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f2963,plain,(
    ! [X0,X1] :
      ( sP0(o_0_0_xboole_0,X0,k8_relat_1(o_0_0_xboole_0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f2948,f79])).

fof(f2948,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_xboole_0(X10)
      | sP0(o_0_0_xboole_0,X9,k8_relat_1(X10,X8))
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f1678,f101])).

fof(f1678,plain,(
    ! [X14,X15,X16] :
      ( r2_hidden(sK10(o_0_0_xboole_0,X14,k8_relat_1(X15,X16)),X15)
      | ~ v1_relat_1(X16)
      | sP0(o_0_0_xboole_0,X14,k8_relat_1(X15,X16)) ) ),
    inference(resolution,[],[f1060,f158])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(X3,X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f157,f89])).

fof(f157,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f156,f86])).

fof(f156,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k8_relat_1(X1,X0))
      | ~ v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f116,f95])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ sP1(k8_relat_1(X1,X2),X1,X2)
      | sP0(X2,X1,k8_relat_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1060,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK9(o_0_0_xboole_0,X2,X3),sK10(o_0_0_xboole_0,X2,X3)),X3)
      | sP0(o_0_0_xboole_0,X2,X3) ) ),
    inference(resolution,[],[f721,f79])).

fof(f721,plain,(
    ! [X47,X48,X49] :
      ( ~ v1_xboole_0(X47)
      | sP0(X47,X48,X49)
      | r2_hidden(k4_tarski(sK9(X47,X48,X49),sK10(X47,X48,X49)),X49) ) ),
    inference(resolution,[],[f93,f101])).

fof(f213,plain,(
    ! [X10,X8,X9] : r2_relset_1(X8,X9,k8_relat_1(X10,sK8(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))),k8_relat_1(X10,sK8(k1_zfmisc_1(k2_zfmisc_1(X8,X9))))) ),
    inference(resolution,[],[f196,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',reflexivity_r2_relset_1)).

fof(f196,plain,(
    ! [X6,X7,X5] : m1_subset_1(k8_relat_1(X7,sK8(k1_zfmisc_1(k2_zfmisc_1(X5,X6)))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f193,f188])).

fof(f188,plain,(
    ! [X6,X7,X5] : k6_relset_1(X5,X6,X7,sK8(k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) = k8_relat_1(X7,sK8(k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) ),
    inference(resolution,[],[f105,f85])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',redefinition_k6_relset_1)).

fof(f193,plain,(
    ! [X6,X7,X5] : m1_subset_1(k6_relset_1(X5,X6,X7,sK8(k1_zfmisc_1(k2_zfmisc_1(X5,X6)))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(resolution,[],[f106,f85])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k6_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',dt_k6_relset_1)).

fof(f6978,plain,(
    k8_relat_1(o_0_0_xboole_0,sK5) = sK5 ),
    inference(forward_demodulation,[],[f6971,f1425])).

fof(f1425,plain,(
    k8_relat_1(sK3,sK5) = sK5 ),
    inference(subsumption_resolution,[],[f1424,f128])).

fof(f1424,plain,
    ( k8_relat_1(sK3,sK5) = sK5
    | ~ v1_relat_1(sK5) ),
    inference(duplicate_literal_removal,[],[f1422])).

fof(f1422,plain,
    ( k8_relat_1(sK3,sK5) = sK5
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f1420,f165])).

fof(f1420,plain,(
    sP0(sK5,sK3,sK5) ),
    inference(condensation,[],[f1414])).

fof(f1414,plain,(
    ! [X62] :
      ( sP0(sK5,sK3,sK5)
      | sP0(sK5,X62,sK5) ) ),
    inference(resolution,[],[f1019,f76])).

fof(f1019,plain,(
    ! [X24,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | sP0(sK5,sK3,sK5)
      | sP0(X23,X24,X23) ) ),
    inference(resolution,[],[f889,f756])).

fof(f889,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | sP0(sK5,sK3,sK5) ) ),
    inference(resolution,[],[f884,f104])).

fof(f884,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | sP0(sK5,sK3,sK5) ),
    inference(subsumption_resolution,[],[f882,f756])).

fof(f882,plain,
    ( ~ r2_hidden(k4_tarski(sK9(sK5,sK3,sK5),sK10(sK5,sK3,sK5)),sK5)
    | sP0(sK5,sK3,sK5)
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f880])).

fof(f880,plain,
    ( ~ r2_hidden(k4_tarski(sK9(sK5,sK3,sK5),sK10(sK5,sK3,sK5)),sK5)
    | sP0(sK5,sK3,sK5)
    | ~ r2_hidden(k4_tarski(sK9(sK5,sK3,sK5),sK10(sK5,sK3,sK5)),sK5)
    | sP0(sK5,sK3,sK5)
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f94,f842])).

fof(f842,plain,(
    ! [X16] :
      ( r2_hidden(sK10(sK5,X16,sK5),sK3)
      | sP0(sK5,X16,sK5)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f815,f772])).

fof(f772,plain,(
    ! [X33,X32] :
      ( sP0(X32,X33,X32)
      | ~ v1_xboole_0(X32) ) ),
    inference(resolution,[],[f756,f101])).

fof(f815,plain,(
    ! [X16] :
      ( sP0(sK5,X16,sK5)
      | r2_hidden(sK10(sK5,X16,sK5),sK3)
      | v1_xboole_0(sK5)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f771,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k4_tarski(X1,X0),sK5)
      | r2_hidden(X0,sK3)
      | v1_xboole_0(sK5)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f146,f161])).

fof(f161,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k2_zfmisc_1(sK2,sK3))
      | v1_xboole_0(sK5)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(resolution,[],[f132,f76])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f103,f98])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t4_subset)).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X3,X0),k2_zfmisc_1(X2,X1))
      | v1_xboole_0(k2_zfmisc_1(X2,X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f112,f98])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t106_zfmisc_1)).

fof(f771,plain,(
    ! [X30,X31] :
      ( m1_subset_1(k4_tarski(sK9(X30,X31,X30),sK10(X30,X31,X30)),X30)
      | sP0(X30,X31,X30) ) ),
    inference(resolution,[],[f756,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t1_subset)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f6971,plain,(
    k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(sK3,sK5) ),
    inference(resolution,[],[f6814,f3647])).

fof(f3647,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,o_0_0_xboole_0)
      | k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(X0,sK5) ) ),
    inference(resolution,[],[f3642,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t36_relset_1.p',t3_subset)).

fof(f3642,plain,(
    ! [X68] :
      ( ~ m1_subset_1(X68,k1_zfmisc_1(o_0_0_xboole_0))
      | k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(X68,sK5) ) ),
    inference(resolution,[],[f3490,f128])).

fof(f3490,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(X8,X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(o_0_0_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f3488,f200])).

fof(f200,plain,(
    ! [X5] : v1_relat_1(k8_relat_1(X5,sK5)) ),
    inference(resolution,[],[f195,f102])).

fof(f195,plain,(
    ! [X4] : m1_subset_1(k8_relat_1(X4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(forward_demodulation,[],[f192,f187])).

fof(f187,plain,(
    ! [X4] : k6_relset_1(sK2,sK3,X4,sK5) = k8_relat_1(X4,sK5) ),
    inference(resolution,[],[f105,f76])).

fof(f192,plain,(
    ! [X4] : m1_subset_1(k6_relset_1(sK2,sK3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f106,f76])).

fof(f3488,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(o_0_0_xboole_0))
      | k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(X8,X9)
      | ~ v1_relat_1(k8_relat_1(o_0_0_xboole_0,sK5))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f3485,f165])).

fof(f3485,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,k8_relat_1(o_0_0_xboole_0,sK5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(o_0_0_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f3481,f200])).

fof(f3481,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,k8_relat_1(o_0_0_xboole_0,sK5))
      | ~ v1_relat_1(k8_relat_1(X0,sK5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(o_0_0_xboole_0)) ) ),
    inference(superposition,[],[f3172,f3217])).

fof(f3217,plain,(
    ! [X51] : k8_relat_1(o_0_0_xboole_0,sK5) = k8_relat_1(o_0_0_xboole_0,k8_relat_1(X51,sK5)) ),
    inference(resolution,[],[f3201,f200])).

fof(f3172,plain,(
    ! [X26,X24,X25] :
      ( sP0(X24,X25,k8_relat_1(o_0_0_xboole_0,X26))
      | ~ v1_relat_1(X26)
      | ~ m1_subset_1(X25,k1_zfmisc_1(o_0_0_xboole_0)) ) ),
    inference(resolution,[],[f2971,f131])).

fof(f6814,plain,(
    r1_tarski(sK3,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f6813,f77])).

fof(f77,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f6813,plain,(
    o_0_0_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f6767,f154])).

fof(f154,plain,(
    r2_relset_1(sK2,sK3,sK5,sK5) ),
    inference(resolution,[],[f119,f76])).

fof(f6767,plain,
    ( ~ r2_relset_1(sK2,sK3,sK5,sK5)
    | o_0_0_xboole_0 = sK4 ),
    inference(superposition,[],[f190,f6514])).

fof(f6514,plain,
    ( k8_relat_1(sK4,sK5) = sK5
    | o_0_0_xboole_0 = sK4 ),
    inference(resolution,[],[f6511,f121])).

fof(f6511,plain,
    ( v1_xboole_0(sK4)
    | k8_relat_1(sK4,sK5) = sK5 ),
    inference(subsumption_resolution,[],[f6510,f128])).

fof(f6510,plain,
    ( v1_xboole_0(sK4)
    | k8_relat_1(sK4,sK5) = sK5
    | ~ v1_relat_1(sK5) ),
    inference(duplicate_literal_removal,[],[f6508])).

fof(f6508,plain,
    ( v1_xboole_0(sK4)
    | k8_relat_1(sK4,sK5) = sK5
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f6485,f165])).

fof(f6485,plain,
    ( sP0(sK5,sK4,sK5)
    | v1_xboole_0(sK4) ),
    inference(duplicate_literal_removal,[],[f6481])).

fof(f6481,plain,
    ( v1_xboole_0(sK4)
    | sP0(sK5,sK4,sK5)
    | sP0(sK5,sK4,sK5) ),
    inference(resolution,[],[f6466,f1666])).

fof(f1666,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(sK5,X0,sK5),sK4)
      | sP0(sK5,X0,sK5) ) ),
    inference(resolution,[],[f1665,f77])).

fof(f1665,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3,X1)
      | m1_subset_1(sK10(sK5,X0,sK5),X1)
      | sP0(sK5,X0,sK5) ) ),
    inference(resolution,[],[f1533,f99])).

fof(f1533,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
      | sP0(sK5,X3,sK5)
      | m1_subset_1(sK10(sK5,X3,sK5),X4) ) ),
    inference(resolution,[],[f1524,f103])).

fof(f1524,plain,(
    ! [X6] :
      ( r2_hidden(sK10(sK5,X6,sK5),sK3)
      | sP0(sK5,X6,sK5) ) ),
    inference(resolution,[],[f1423,f756])).

fof(f1423,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK5)
      | r2_hidden(X3,sK3) ) ),
    inference(resolution,[],[f1420,f89])).

fof(f6466,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK10(X0,X1,X0),X1)
      | v1_xboole_0(X1)
      | sP0(X0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f6465,f756])).

fof(f6465,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,X0)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1,X0),sK10(X0,X1,X0)),X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK10(X0,X1,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f6440])).

fof(f6440,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,X0)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1,X0),sK10(X0,X1,X0)),X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK10(X0,X1,X0),X1)
      | sP0(X0,X1,X0) ) ),
    inference(resolution,[],[f881,f756])).

fof(f881,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK9(X2,X3,X4),sK10(X2,X3,X4)),X4)
      | sP0(X2,X3,X4)
      | ~ r2_hidden(k4_tarski(sK9(X2,X3,X4),sK10(X2,X3,X4)),X2)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK10(X2,X3,X4),X3) ) ),
    inference(resolution,[],[f94,f98])).

fof(f190,plain,(
    ~ r2_relset_1(sK2,sK3,k8_relat_1(sK4,sK5),sK5) ),
    inference(backward_demodulation,[],[f187,f78])).

fof(f78,plain,(
    ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f7278,plain,(
    ~ r2_relset_1(sK2,sK3,sK5,sK5) ),
    inference(backward_demodulation,[],[f6978,f6820])).

fof(f6820,plain,(
    ~ r2_relset_1(sK2,sK3,k8_relat_1(o_0_0_xboole_0,sK5),sK5) ),
    inference(backward_demodulation,[],[f6813,f190])).
%------------------------------------------------------------------------------
