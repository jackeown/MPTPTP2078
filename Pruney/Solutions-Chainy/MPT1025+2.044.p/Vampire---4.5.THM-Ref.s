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
% DateTime   : Thu Dec  3 13:06:27 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 723 expanded)
%              Number of leaves         :   22 ( 219 expanded)
%              Depth                    :   15
%              Number of atoms          :  444 (3770 expanded)
%              Number of equality atoms :   26 ( 547 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f142,f157,f226])).

fof(f226,plain,
    ( ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f221,f215])).

fof(f215,plain,
    ( sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f167,f168,f59])).

fof(f59,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | k1_funct_1(sK3,X5) != sK4 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (17897)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f38,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f168,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f138,f97,f90,f124])).

fof(f124,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X7,sK1)
        | v1_xboole_0(X6)
        | ~ r2_hidden(X7,k9_relat_1(sK3,X6))
        | r2_hidden(sK5(X6,sK0,sK3,X7),X6) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl10_5
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X7,k9_relat_1(sK3,X6))
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X7,sK1)
        | r2_hidden(sK5(X6,sK0,sK3,X7),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f90,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f58,f88])).

fof(f88,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f57,f82])).

fof(f82,plain,(
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

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(unit_resulting_resolution,[],[f90,f91,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f87,f88])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f138,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
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

fof(f95,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f90,f89,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f67,f57,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f167,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f138,f97,f90,f114])).

% (17903)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f114,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,sK1)
        | v1_xboole_0(X2)
        | ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl10_3
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f221,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f89,f56,f169,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f169,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f138,f97,f90,f119])).

fof(f119,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,sK1)
        | v1_xboole_0(X4)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl10_4
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f157,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f155,f145])).

fof(f145,plain,
    ( v1_xboole_0(sK3)
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f57,f107,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f107,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl10_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f155,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f94,f65])).

fof(f94,plain,(
    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    inference(unit_resulting_resolution,[],[f90,f89,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f142,plain,(
    ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f139,f137])).

fof(f137,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f132,f65])).

fof(f132,plain,
    ( v1_xboole_0(sK3)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f57,f111,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f111,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f139,plain,(
    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),k1_funct_1(sK3,sK8(sK4,sK2,sK3))),sK3) ),
    inference(unit_resulting_resolution,[],[f89,f56,f93,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f90,f89,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f125,plain,
    ( spl10_1
    | spl10_2
    | spl10_5 ),
    inference(avatar_split_clause,[],[f121,f123,f109,f105])).

fof(f121,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k9_relat_1(sK3,X6))
      | r2_hidden(sK5(X6,sK0,sK3,X7),X6)
      | ~ m1_subset_1(X7,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X6)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k9_relat_1(sK3,X6))
      | r2_hidden(sK5(X6,sK0,sK3,X7),X6)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X6)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f62,f88])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK5(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK5(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK5(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK5(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f120,plain,
    ( spl10_1
    | spl10_2
    | spl10_4 ),
    inference(avatar_split_clause,[],[f116,f118,f109,f105])).

fof(f116,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3)
      | ~ m1_subset_1(X5,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f100,f57])).

fof(f100,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3)
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f61,f88])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,
    ( spl10_1
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f103,f113,f109,f105])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0)
      | ~ m1_subset_1(X3,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f99,f57])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0)
      | ~ m1_subset_1(X3,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X2)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f60,f88])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (17896)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (17904)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (17888)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (17886)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (17901)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  % (17895)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.52  % (17889)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.52  % (17885)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (17902)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.53  % (17906)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.53  % (17893)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.53  % (17894)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (17909)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.53  % (17910)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (17898)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.53  % (17907)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.54  % (17893)Refutation not found, incomplete strategy% (17893)------------------------------
% 1.25/0.54  % (17893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (17893)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (17893)Memory used [KB]: 10618
% 1.25/0.54  % (17893)Time elapsed: 0.121 s
% 1.25/0.54  % (17893)------------------------------
% 1.25/0.54  % (17893)------------------------------
% 1.25/0.54  % (17883)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.54  % (17885)Refutation not found, incomplete strategy% (17885)------------------------------
% 1.25/0.54  % (17885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (17885)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (17885)Memory used [KB]: 10746
% 1.25/0.54  % (17885)Time elapsed: 0.087 s
% 1.25/0.54  % (17885)------------------------------
% 1.25/0.54  % (17885)------------------------------
% 1.25/0.54  % (17887)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.54  % (17905)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.54  % (17890)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (17912)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % (17908)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.54  % (17899)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.54  % (17884)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.55  % (17900)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.55  % (17891)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.55  % (17911)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.55  % (17894)Refutation not found, incomplete strategy% (17894)------------------------------
% 1.39/0.55  % (17894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (17894)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (17894)Memory used [KB]: 10618
% 1.39/0.55  % (17894)Time elapsed: 0.135 s
% 1.39/0.55  % (17894)------------------------------
% 1.39/0.55  % (17894)------------------------------
% 1.39/0.55  % (17892)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.55  % (17909)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f227,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(avatar_sat_refutation,[],[f115,f120,f125,f142,f157,f226])).
% 1.39/0.55  fof(f226,plain,(
% 1.39/0.55    ~spl10_3 | ~spl10_4 | ~spl10_5),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f225])).
% 1.39/0.55  fof(f225,plain,(
% 1.39/0.55    $false | (~spl10_3 | ~spl10_4 | ~spl10_5)),
% 1.39/0.55    inference(subsumption_resolution,[],[f221,f215])).
% 1.39/0.55  fof(f215,plain,(
% 1.39/0.55    sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | (~spl10_3 | ~spl10_5)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f167,f168,f59])).
% 1.39/0.55  fof(f59,plain,(
% 1.39/0.55    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | k1_funct_1(sK3,X5) != sK4) )),
% 1.39/0.55    inference(cnf_transformation,[],[f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f38,f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.56  % (17897)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.39/0.56    inference(flattening,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.39/0.56    inference(ennf_transformation,[],[f18])).
% 1.39/0.56  fof(f18,plain,(
% 1.39/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.39/0.56    inference(pure_predicate_removal,[],[f16])).
% 1.39/0.56  fof(f16,negated_conjecture,(
% 1.39/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.39/0.56    inference(negated_conjecture,[],[f15])).
% 1.39/0.56  fof(f15,conjecture,(
% 1.39/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 1.39/0.56  fof(f168,plain,(
% 1.39/0.56    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~spl10_5),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f138,f97,f90,f124])).
% 1.39/0.56  fof(f124,plain,(
% 1.39/0.56    ( ! [X6,X7] : (~m1_subset_1(X7,sK1) | v1_xboole_0(X6) | ~r2_hidden(X7,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X6,sK0,sK3,X7),X6)) ) | ~spl10_5),
% 1.39/0.56    inference(avatar_component_clause,[],[f123])).
% 1.39/0.56  fof(f123,plain,(
% 1.39/0.56    spl10_5 <=> ! [X7,X6] : (~r2_hidden(X7,k9_relat_1(sK3,X6)) | v1_xboole_0(X6) | ~m1_subset_1(X7,sK1) | r2_hidden(sK5(X6,sK0,sK3,X7),X6))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.39/0.56  fof(f90,plain,(
% 1.39/0.56    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.39/0.56    inference(backward_demodulation,[],[f58,f88])).
% 1.39/0.56  fof(f88,plain,(
% 1.39/0.56    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f57,f82])).
% 1.39/0.56  fof(f82,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,axiom,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.56    inference(cnf_transformation,[],[f39])).
% 1.39/0.56  fof(f58,plain,(
% 1.39/0.56    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.39/0.56    inference(cnf_transformation,[],[f39])).
% 1.39/0.56  fof(f97,plain,(
% 1.39/0.56    m1_subset_1(sK4,sK1)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f90,f91,f80])).
% 1.39/0.56  fof(f80,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.39/0.56    inference(flattening,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.39/0.56    inference(ennf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.39/0.56  fof(f91,plain,(
% 1.39/0.56    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.39/0.56    inference(forward_demodulation,[],[f87,f88])).
% 1.39/0.56  fof(f87,plain,(
% 1.39/0.56    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f57,f81])).
% 1.39/0.56  fof(f81,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f33])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.39/0.56  fof(f138,plain,(
% 1.39/0.56    ~v1_xboole_0(sK2)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f95,f65])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f47])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.56    inference(rectify,[],[f44])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.39/0.56  fof(f95,plain,(
% 1.39/0.56    r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f90,f89,f75])).
% 1.39/0.56  fof(f75,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f53])).
% 1.39/0.56  fof(f53,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).
% 1.39/0.56  fof(f52,plain,(
% 1.39/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(rectify,[],[f50])).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(nnf_transformation,[],[f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(ennf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.39/0.56  fof(f89,plain,(
% 1.39/0.56    v1_relat_1(sK3)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f67,f57,f64])).
% 1.39/0.56  fof(f64,plain,(
% 1.39/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.39/0.56  fof(f67,plain,(
% 1.39/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.56  fof(f167,plain,(
% 1.39/0.56    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl10_3),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f138,f97,f90,f114])).
% 1.39/0.56  % (17903)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.56  fof(f114,plain,(
% 1.39/0.56    ( ! [X2,X3] : (~m1_subset_1(X3,sK1) | v1_xboole_0(X2) | ~r2_hidden(X3,k9_relat_1(sK3,X2)) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0)) ) | ~spl10_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f113])).
% 1.39/0.56  fof(f113,plain,(
% 1.39/0.56    spl10_3 <=> ! [X3,X2] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.39/0.56  fof(f221,plain,(
% 1.39/0.56    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~spl10_4),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f89,f56,f169,f78])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f55])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(flattening,[],[f54])).
% 1.39/0.56  fof(f54,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(nnf_transformation,[],[f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.39/0.56    inference(flattening,[],[f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.39/0.56    inference(ennf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.39/0.56  fof(f169,plain,(
% 1.39/0.56    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl10_4),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f138,f97,f90,f119])).
% 1.39/0.56  fof(f119,plain,(
% 1.39/0.56    ( ! [X4,X5] : (~m1_subset_1(X5,sK1) | v1_xboole_0(X4) | ~r2_hidden(X5,k9_relat_1(sK3,X4)) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3)) ) | ~spl10_4),
% 1.39/0.56    inference(avatar_component_clause,[],[f118])).
% 1.39/0.56  fof(f118,plain,(
% 1.39/0.56    spl10_4 <=> ! [X5,X4] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    v1_funct_1(sK3)),
% 1.39/0.56    inference(cnf_transformation,[],[f39])).
% 1.39/0.56  fof(f157,plain,(
% 1.39/0.56    ~spl10_1),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f156])).
% 1.39/0.56  fof(f156,plain,(
% 1.39/0.56    $false | ~spl10_1),
% 1.39/0.56    inference(subsumption_resolution,[],[f155,f145])).
% 1.39/0.56  fof(f145,plain,(
% 1.39/0.56    v1_xboole_0(sK3) | ~spl10_1),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f57,f107,f68])).
% 1.39/0.56  fof(f68,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.39/0.56  fof(f107,plain,(
% 1.39/0.56    v1_xboole_0(sK1) | ~spl10_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f105])).
% 1.39/0.56  fof(f105,plain,(
% 1.39/0.56    spl10_1 <=> v1_xboole_0(sK1)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.39/0.56  fof(f155,plain,(
% 1.39/0.56    ~v1_xboole_0(sK3)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f94,f65])).
% 1.39/0.56  fof(f94,plain,(
% 1.39/0.56    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f90,f89,f74])).
% 1.39/0.56  fof(f74,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f53])).
% 1.39/0.56  fof(f142,plain,(
% 1.39/0.56    ~spl10_2),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f141])).
% 1.39/0.56  fof(f141,plain,(
% 1.39/0.56    $false | ~spl10_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f139,f137])).
% 1.39/0.56  fof(f137,plain,(
% 1.39/0.56    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl10_2),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f132,f65])).
% 1.39/0.56  fof(f132,plain,(
% 1.39/0.56    v1_xboole_0(sK3) | ~spl10_2),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f57,f111,f69])).
% 1.39/0.56  fof(f69,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.39/0.56  fof(f111,plain,(
% 1.39/0.56    v1_xboole_0(sK0) | ~spl10_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f109])).
% 1.39/0.56  fof(f109,plain,(
% 1.39/0.56    spl10_2 <=> v1_xboole_0(sK0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.39/0.56  fof(f139,plain,(
% 1.39/0.56    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),k1_funct_1(sK3,sK8(sK4,sK2,sK3))),sK3)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f89,f56,f93,f84])).
% 1.39/0.56  fof(f84,plain,(
% 1.39/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.56    inference(equality_resolution,[],[f79])).
% 1.39/0.56  fof(f79,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f55])).
% 1.39/0.56  fof(f93,plain,(
% 1.39/0.56    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f90,f89,f73])).
% 1.39/0.56  fof(f73,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f53])).
% 1.39/0.56  fof(f125,plain,(
% 1.39/0.56    spl10_1 | spl10_2 | spl10_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f121,f123,f109,f105])).
% 1.39/0.56  fof(f121,plain,(
% 1.39/0.56    ( ! [X6,X7] : (~r2_hidden(X7,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X6,sK0,sK3,X7),X6) | ~m1_subset_1(X7,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X6) | v1_xboole_0(sK1)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f101,f57])).
% 1.39/0.56  fof(f101,plain,(
% 1.39/0.56    ( ! [X6,X7] : (~r2_hidden(X7,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X6,sK0,sK3,X7),X6) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X6) | v1_xboole_0(sK1)) )),
% 1.39/0.56    inference(superposition,[],[f62,f88])).
% 1.39/0.56  fof(f62,plain,(
% 1.39/0.56    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f43])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f41,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.39/0.56    inference(rectify,[],[f40])).
% 1.39/0.56  fof(f40,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f14])).
% 1.39/0.56  fof(f14,axiom,(
% 1.39/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 1.39/0.56  fof(f120,plain,(
% 1.39/0.56    spl10_1 | spl10_2 | spl10_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f116,f118,f109,f105])).
% 1.39/0.56  fof(f116,plain,(
% 1.39/0.56    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) | ~m1_subset_1(X5,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X4) | v1_xboole_0(sK1)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f100,f57])).
% 1.39/0.56  fof(f100,plain,(
% 1.39/0.56    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) | ~m1_subset_1(X5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X4) | v1_xboole_0(sK1)) )),
% 1.39/0.56    inference(superposition,[],[f61,f88])).
% 1.39/0.56  fof(f61,plain,(
% 1.39/0.56    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f43])).
% 1.39/0.56  fof(f115,plain,(
% 1.39/0.56    spl10_1 | spl10_2 | spl10_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f103,f113,f109,f105])).
% 1.39/0.56  fof(f103,plain,(
% 1.39/0.56    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) | ~m1_subset_1(X3,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | v1_xboole_0(sK1)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f99,f57])).
% 1.39/0.56  fof(f99,plain,(
% 1.39/0.56    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) | ~m1_subset_1(X3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X2) | v1_xboole_0(sK1)) )),
% 1.39/0.56    inference(superposition,[],[f60,f88])).
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f43])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (17909)------------------------------
% 1.39/0.56  % (17909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (17909)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (17909)Memory used [KB]: 11001
% 1.39/0.56  % (17909)Time elapsed: 0.141 s
% 1.39/0.56  % (17909)------------------------------
% 1.39/0.56  % (17909)------------------------------
% 1.39/0.56  % (17905)Refutation not found, incomplete strategy% (17905)------------------------------
% 1.39/0.56  % (17905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (17905)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (17905)Memory used [KB]: 10874
% 1.39/0.56  % (17905)Time elapsed: 0.144 s
% 1.39/0.56  % (17905)------------------------------
% 1.39/0.56  % (17905)------------------------------
% 1.39/0.56  % (17882)Success in time 0.2 s
%------------------------------------------------------------------------------
