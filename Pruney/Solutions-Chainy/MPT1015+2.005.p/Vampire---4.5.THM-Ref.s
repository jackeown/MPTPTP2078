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
% DateTime   : Thu Dec  3 13:05:26 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  240 (2150 expanded)
%              Number of leaves         :   28 ( 665 expanded)
%              Depth                    :   44
%              Number of atoms          :  944 (16260 expanded)
%              Number of equality atoms :  164 ( 467 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1664,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f245,f490,f523,f593,f750,f863,f1381,f1663])).

fof(f1663,plain,
    ( spl3_30
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f1662])).

fof(f1662,plain,
    ( $false
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1661,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f49,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & v2_funct_1(sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & v2_funct_1(sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f1661,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1660,f762])).

fof(f762,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f59,f485])).

fof(f485,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl3_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1660,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1659,f763])).

fof(f763,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f60,f485])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f1659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1658,f55])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1658,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1657,f760])).

fof(f760,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f56,f485])).

fof(f56,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1657,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1656,f761])).

fof(f761,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f57,f485])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f1656,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1655,f480])).

fof(f480,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl3_30
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1655,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1647,f62])).

fof(f62,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1647,plain,
    ( ~ v2_funct_1(sK1)
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f94,f1645])).

fof(f1645,plain,
    ( sK1 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,sK1)
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f581,f485])).

fof(f581,plain,(
    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f376,f567])).

fof(f567,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f547,f445])).

fof(f445,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) ),
    inference(backward_demodulation,[],[f61,f376])).

fof(f61,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f547,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) ),
    inference(resolution,[],[f467,f165])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK1 = X0
      | ~ r2_relset_1(sK0,sK0,X0,sK1) ) ),
    inference(resolution,[],[f86,f57])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f467,plain,(
    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f466,f58])).

fof(f466,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f465,f60])).

fof(f465,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f464,f55])).

fof(f464,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f449,f57])).

fof(f449,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f90,f376])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f376,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f373,f58])).

fof(f373,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f276,f60])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f274,f55])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f88,f57])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f94,plain,(
    ! [X4,X2,X0,X3] :
      ( ~ v2_funct_1(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,X2,X3,X4))
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ v1_funct_2(X4,k1_xboole_0,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X3,X0,k1_xboole_0)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f1381,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | spl3_33
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f1380])).

fof(f1380,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | spl3_33
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1379,f172])).

fof(f172,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f137,f158])).

fof(f158,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f157,f58])).

fof(f157,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f154,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f76,f60])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f137,plain,(
    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f81,f60])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1379,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | spl3_33
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1378,f628])).

fof(f628,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f627,f172])).

fof(f627,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f626,f98])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f60])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f626,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f614,f58])).

fof(f614,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(resolution,[],[f481,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f481,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f479])).

fof(f1378,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | spl3_33
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1377,f509])).

fof(f509,plain,
    ( sK2 != k6_relat_1(sK0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl3_33
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1377,plain,
    ( sK2 = k6_relat_1(sK0)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1376,f172])).

fof(f1376,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1375,f711])).

fof(f711,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f710])).

fof(f710,plain,
    ( spl3_44
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1375,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1374,f715])).

fof(f715,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl3_45
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f1374,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1373,f98])).

fof(f1373,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1359,f58])).

fof(f1359,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(trivial_inequality_removal,[],[f1357])).

fof(f1357,plain,
    ( k2_funct_1(sK2) != k2_funct_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(superposition,[],[f72,f1350])).

fof(f1350,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1293,f1331])).

fof(f1331,plain,
    ( k6_relat_1(sK0) = k2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1330,f164])).

fof(f164,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f115,f159])).

fof(f159,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f136,f156])).

fof(f156,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f155,f55])).

fof(f155,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f153,f56])).

fof(f153,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f76,f57])).

fof(f136,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f81,f57])).

fof(f115,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f114,f97])).

fof(f97,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f80,f57])).

fof(f114,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f113,f55])).

fof(f113,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f68,f62])).

fof(f1330,plain,
    ( sK0 != k2_relat_1(k2_funct_1(sK1))
    | k6_relat_1(sK0) = k2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1292,f983])).

fof(f983,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f630,f648])).

fof(f648,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f647,f98])).

fof(f647,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f645,f107])).

fof(f107,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f83,f60])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f645,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f608,f103])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f608,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f607,f159])).

fof(f607,plain,(
    r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f606,f97])).

fof(f606,plain,
    ( r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f605,f55])).

fof(f605,plain,
    ( r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f604,f98])).

fof(f604,plain,
    ( r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f603,f58])).

fof(f603,plain,
    ( r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f591,f62])).

fof(f591,plain,
    ( ~ v2_funct_1(sK1)
    | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f590])).

fof(f590,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f73,f567])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(f630,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f629,f98])).

fof(f629,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f615,f58])).

fof(f615,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(resolution,[],[f481,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1292,plain,
    ( k6_relat_1(sK0) = k2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1291,f983])).

fof(f1291,plain,
    ( k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1290,f121])).

fof(f121,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_1
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1290,plain,
    ( k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1289,f225])).

fof(f225,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl3_7
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1289,plain,
    ( k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_30
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1288,f711])).

fof(f1288,plain,
    ( k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1287,f715])).

fof(f1287,plain,
    ( k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_30 ),
    inference(trivial_inequality_removal,[],[f1285])).

fof(f1285,plain,
    ( k2_funct_1(sK1) != k2_funct_1(sK1)
    | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_30 ),
    inference(superposition,[],[f72,f618])).

fof(f618,plain,
    ( k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f617,f567])).

fof(f617,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f616,f98])).

fof(f616,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f610,f58])).

fof(f610,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(resolution,[],[f481,f175])).

fof(f175,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f174,f97])).

fof(f174,plain,(
    ! [X0] :
      ( k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f173,f55])).

fof(f173,plain,(
    ! [X0] :
      ( k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f71,f62])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(f1293,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f622,f648])).

fof(f622,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f621,f98])).

fof(f621,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f612,f58])).

fof(f612,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(resolution,[],[f481,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f863,plain,(
    spl3_45 ),
    inference(avatar_contradiction_clause,[],[f862])).

fof(f862,plain,
    ( $false
    | spl3_45 ),
    inference(subsumption_resolution,[],[f861,f98])).

fof(f861,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_45 ),
    inference(subsumption_resolution,[],[f860,f58])).

fof(f860,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_45 ),
    inference(resolution,[],[f716,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f716,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f714])).

fof(f750,plain,(
    spl3_44 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | spl3_44 ),
    inference(subsumption_resolution,[],[f748,f98])).

fof(f748,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_44 ),
    inference(subsumption_resolution,[],[f747,f58])).

fof(f747,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_44 ),
    inference(resolution,[],[f712,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f712,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f710])).

fof(f593,plain,(
    spl3_32 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | spl3_32 ),
    inference(subsumption_resolution,[],[f588,f62])).

fof(f588,plain,
    ( ~ v2_funct_1(sK1)
    | spl3_32 ),
    inference(backward_demodulation,[],[f489,f567])).

fof(f489,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl3_32
  <=> v2_funct_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f523,plain,(
    ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f520,f109])).

fof(f109,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f96,f60])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f520,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f91,f510])).

fof(f510,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f508])).

fof(f91,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f490,plain,
    ( spl3_30
    | spl3_31
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f477,f487,f483,f479])).

fof(f477,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f476,f58])).

fof(f476,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f475,f59])).

fof(f475,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f474,f60])).

fof(f474,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f473,f55])).

fof(f473,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f472,f56])).

fof(f472,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f451,f57])).

fof(f451,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f84,f376])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f245,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f243,f97])).

fof(f243,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f242,f55])).

fof(f242,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(resolution,[],[f226,f66])).

fof(f226,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f224])).

fof(f141,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f139,f97])).

fof(f139,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f138,f55])).

fof(f138,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f122,f65])).

fof(f122,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (27288)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (27293)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.56  % (27309)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.56  % (27296)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.51/0.56  % (27282)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.51/0.56  % (27286)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.51/0.57  % (27292)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.51/0.57  % (27283)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.51/0.57  % (27301)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.57  % (27294)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.51/0.57  % (27306)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.51/0.57  % (27290)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.51/0.58  % (27304)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.51/0.58  % (27311)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.51/0.58  % (27305)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.51/0.58  % (27289)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.58  % (27297)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.51/0.58  % (27299)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.58  % (27287)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.59  % (27307)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.59  % (27302)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.51/0.59  % (27291)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.59  % (27285)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.51/0.59  % (27284)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.51/0.59  % (27298)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.51/0.59  % (27295)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.51/0.59  % (27310)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.51/0.59  % (27298)Refutation not found, incomplete strategy% (27298)------------------------------
% 1.51/0.59  % (27298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (27298)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (27298)Memory used [KB]: 10746
% 1.51/0.59  % (27298)Time elapsed: 0.165 s
% 1.51/0.59  % (27298)------------------------------
% 1.51/0.59  % (27298)------------------------------
% 1.51/0.60  % (27303)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.51/0.60  % (27308)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.60  % (27300)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.63  % (27288)Refutation found. Thanks to Tanya!
% 1.51/0.63  % SZS status Theorem for theBenchmark
% 1.51/0.63  % SZS output start Proof for theBenchmark
% 1.51/0.63  fof(f1664,plain,(
% 1.51/0.63    $false),
% 1.51/0.63    inference(avatar_sat_refutation,[],[f141,f245,f490,f523,f593,f750,f863,f1381,f1663])).
% 1.51/0.63  fof(f1663,plain,(
% 1.51/0.63    spl3_30 | ~spl3_31),
% 1.51/0.63    inference(avatar_contradiction_clause,[],[f1662])).
% 1.51/0.63  fof(f1662,plain,(
% 1.51/0.63    $false | (spl3_30 | ~spl3_31)),
% 1.51/0.63    inference(subsumption_resolution,[],[f1661,f58])).
% 1.51/0.63  fof(f58,plain,(
% 1.51/0.63    v1_funct_1(sK2)),
% 1.51/0.63    inference(cnf_transformation,[],[f50])).
% 1.51/0.63  fof(f50,plain,(
% 1.51/0.63    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.51/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f49,f48])).
% 1.51/0.63  fof(f48,plain,(
% 1.51/0.63    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.51/0.63    introduced(choice_axiom,[])).
% 1.51/0.63  fof(f49,plain,(
% 1.51/0.63    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.51/0.63    introduced(choice_axiom,[])).
% 1.51/0.63  fof(f21,plain,(
% 1.51/0.63    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.51/0.63    inference(flattening,[],[f20])).
% 1.51/0.63  fof(f20,plain,(
% 1.51/0.63    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.51/0.63    inference(ennf_transformation,[],[f19])).
% 1.51/0.63  fof(f19,negated_conjecture,(
% 1.51/0.63    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.51/0.63    inference(negated_conjecture,[],[f18])).
% 1.51/0.63  fof(f18,conjecture,(
% 1.51/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.51/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 1.51/0.63  fof(f1661,plain,(
% 1.51/0.63    ~v1_funct_1(sK2) | (spl3_30 | ~spl3_31)),
% 1.51/0.63    inference(subsumption_resolution,[],[f1660,f762])).
% 1.51/0.63  fof(f762,plain,(
% 1.51/0.63    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_31),
% 1.51/0.63    inference(backward_demodulation,[],[f59,f485])).
% 1.51/0.63  fof(f485,plain,(
% 1.51/0.63    k1_xboole_0 = sK0 | ~spl3_31),
% 1.51/0.63    inference(avatar_component_clause,[],[f483])).
% 1.51/0.63  fof(f483,plain,(
% 1.51/0.63    spl3_31 <=> k1_xboole_0 = sK0),
% 1.51/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.51/0.63  fof(f59,plain,(
% 1.51/0.63    v1_funct_2(sK2,sK0,sK0)),
% 1.51/0.63    inference(cnf_transformation,[],[f50])).
% 1.51/0.63  fof(f1660,plain,(
% 1.51/0.63    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (spl3_30 | ~spl3_31)),
% 1.51/0.63    inference(subsumption_resolution,[],[f1659,f763])).
% 1.51/0.63  fof(f763,plain,(
% 1.51/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_31),
% 1.51/0.63    inference(backward_demodulation,[],[f60,f485])).
% 1.51/0.63  fof(f60,plain,(
% 1.51/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.63    inference(cnf_transformation,[],[f50])).
% 1.51/0.63  fof(f1659,plain,(
% 1.51/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (spl3_30 | ~spl3_31)),
% 1.51/0.63    inference(subsumption_resolution,[],[f1658,f55])).
% 1.51/0.63  fof(f55,plain,(
% 1.51/0.63    v1_funct_1(sK1)),
% 1.51/0.63    inference(cnf_transformation,[],[f50])).
% 1.51/0.63  fof(f1658,plain,(
% 1.51/0.63    ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (spl3_30 | ~spl3_31)),
% 1.51/0.63    inference(subsumption_resolution,[],[f1657,f760])).
% 1.51/0.63  fof(f760,plain,(
% 1.51/0.63    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl3_31),
% 1.51/0.63    inference(backward_demodulation,[],[f56,f485])).
% 1.51/0.63  fof(f56,plain,(
% 1.51/0.63    v1_funct_2(sK1,sK0,sK0)),
% 1.51/0.63    inference(cnf_transformation,[],[f50])).
% 1.51/0.63  fof(f1657,plain,(
% 1.51/0.63    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (spl3_30 | ~spl3_31)),
% 1.51/0.63    inference(subsumption_resolution,[],[f1656,f761])).
% 1.51/0.63  fof(f761,plain,(
% 1.51/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_31),
% 1.51/0.63    inference(backward_demodulation,[],[f57,f485])).
% 1.51/0.63  fof(f57,plain,(
% 1.51/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.63    inference(cnf_transformation,[],[f50])).
% 1.51/0.64  fof(f1656,plain,(
% 1.51/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (spl3_30 | ~spl3_31)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1655,f480])).
% 1.51/0.64  fof(f480,plain,(
% 1.51/0.64    ~v2_funct_1(sK2) | spl3_30),
% 1.51/0.64    inference(avatar_component_clause,[],[f479])).
% 1.51/0.64  fof(f479,plain,(
% 1.51/0.64    spl3_30 <=> v2_funct_1(sK2)),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.51/0.64  fof(f1655,plain,(
% 1.51/0.64    v2_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_31),
% 1.51/0.64    inference(subsumption_resolution,[],[f1647,f62])).
% 1.51/0.64  fof(f62,plain,(
% 1.51/0.64    v2_funct_1(sK1)),
% 1.51/0.64    inference(cnf_transformation,[],[f50])).
% 1.51/0.64  fof(f1647,plain,(
% 1.51/0.64    ~v2_funct_1(sK1) | v2_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_31),
% 1.51/0.64    inference(superposition,[],[f94,f1645])).
% 1.51/0.64  fof(f1645,plain,(
% 1.51/0.64    sK1 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,sK1) | ~spl3_31),
% 1.51/0.64    inference(forward_demodulation,[],[f581,f485])).
% 1.51/0.64  fof(f581,plain,(
% 1.51/0.64    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 1.51/0.64    inference(backward_demodulation,[],[f376,f567])).
% 1.51/0.64  fof(f567,plain,(
% 1.51/0.64    sK1 = k5_relat_1(sK2,sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f547,f445])).
% 1.51/0.64  fof(f445,plain,(
% 1.51/0.64    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)),
% 1.51/0.64    inference(backward_demodulation,[],[f61,f376])).
% 1.51/0.64  fof(f61,plain,(
% 1.51/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 1.51/0.64    inference(cnf_transformation,[],[f50])).
% 1.51/0.64  fof(f547,plain,(
% 1.51/0.64    sK1 = k5_relat_1(sK2,sK1) | ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)),
% 1.51/0.64    inference(resolution,[],[f467,f165])).
% 1.51/0.64  fof(f165,plain,(
% 1.51/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X0 | ~r2_relset_1(sK0,sK0,X0,sK1)) )),
% 1.51/0.64    inference(resolution,[],[f86,f57])).
% 1.51/0.64  fof(f86,plain,(
% 1.51/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f54])).
% 1.51/0.64  fof(f54,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(nnf_transformation,[],[f43])).
% 1.51/0.64  fof(f43,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(flattening,[],[f42])).
% 1.51/0.64  fof(f42,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.51/0.64    inference(ennf_transformation,[],[f12])).
% 1.51/0.64  fof(f12,axiom,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.51/0.64  fof(f467,plain,(
% 1.51/0.64    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.64    inference(subsumption_resolution,[],[f466,f58])).
% 1.51/0.64  fof(f466,plain,(
% 1.51/0.64    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f465,f60])).
% 1.51/0.64  fof(f465,plain,(
% 1.51/0.64    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f464,f55])).
% 1.51/0.64  fof(f464,plain,(
% 1.51/0.64    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f449,f57])).
% 1.51/0.64  fof(f449,plain,(
% 1.51/0.64    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(superposition,[],[f90,f376])).
% 1.51/0.64  fof(f90,plain,(
% 1.51/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f47])).
% 1.51/0.64  fof(f47,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.51/0.64    inference(flattening,[],[f46])).
% 1.51/0.64  fof(f46,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.51/0.64    inference(ennf_transformation,[],[f13])).
% 1.51/0.64  fof(f13,axiom,(
% 1.51/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.51/0.64  fof(f376,plain,(
% 1.51/0.64    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f373,f58])).
% 1.51/0.64  fof(f373,plain,(
% 1.51/0.64    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(resolution,[],[f276,f60])).
% 1.51/0.64  fof(f276,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) | ~v1_funct_1(X2)) )),
% 1.51/0.64    inference(subsumption_resolution,[],[f274,f55])).
% 1.51/0.64  fof(f274,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.51/0.64    inference(resolution,[],[f88,f57])).
% 1.51/0.64  fof(f88,plain,(
% 1.51/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f45])).
% 1.51/0.64  fof(f45,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.51/0.64    inference(flattening,[],[f44])).
% 1.51/0.64  fof(f44,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.51/0.64    inference(ennf_transformation,[],[f14])).
% 1.51/0.64  fof(f14,axiom,(
% 1.51/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.51/0.64  fof(f94,plain,(
% 1.51/0.64    ( ! [X4,X2,X0,X3] : (~v2_funct_1(k1_partfun1(X0,k1_xboole_0,k1_xboole_0,X2,X3,X4)) | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~v1_funct_2(X4,k1_xboole_0,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X3,X0,k1_xboole_0) | ~v1_funct_1(X3)) )),
% 1.51/0.64    inference(equality_resolution,[],[f85])).
% 1.51/0.64  fof(f85,plain,(
% 1.51/0.64    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f41])).
% 1.51/0.64  fof(f41,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.51/0.64    inference(flattening,[],[f40])).
% 1.51/0.64  fof(f40,plain,(
% 1.51/0.64    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.51/0.64    inference(ennf_transformation,[],[f16])).
% 1.51/0.64  fof(f16,axiom,(
% 1.51/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.51/0.64  fof(f1381,plain,(
% 1.51/0.64    ~spl3_1 | ~spl3_7 | ~spl3_30 | spl3_33 | ~spl3_44 | ~spl3_45),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f1380])).
% 1.51/0.64  fof(f1380,plain,(
% 1.51/0.64    $false | (~spl3_1 | ~spl3_7 | ~spl3_30 | spl3_33 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1379,f172])).
% 1.51/0.64  fof(f172,plain,(
% 1.51/0.64    sK0 = k1_relat_1(sK2)),
% 1.51/0.64    inference(backward_demodulation,[],[f137,f158])).
% 1.51/0.64  fof(f158,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f157,f58])).
% 1.51/0.64  fof(f157,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f154,f59])).
% 1.51/0.64  fof(f154,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(resolution,[],[f76,f60])).
% 1.51/0.64  fof(f76,plain,(
% 1.51/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f36])).
% 1.51/0.64  fof(f36,plain,(
% 1.51/0.64    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.51/0.64    inference(flattening,[],[f35])).
% 1.51/0.64  fof(f35,plain,(
% 1.51/0.64    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.51/0.64    inference(ennf_transformation,[],[f17])).
% 1.51/0.64  fof(f17,axiom,(
% 1.51/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.51/0.64  fof(f137,plain,(
% 1.51/0.64    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 1.51/0.64    inference(resolution,[],[f81,f60])).
% 1.51/0.64  fof(f81,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f38])).
% 1.51/0.64  fof(f38,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f11])).
% 1.51/0.64  fof(f11,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.64  fof(f1379,plain,(
% 1.51/0.64    sK0 != k1_relat_1(sK2) | (~spl3_1 | ~spl3_7 | ~spl3_30 | spl3_33 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(forward_demodulation,[],[f1378,f628])).
% 1.51/0.64  fof(f628,plain,(
% 1.51/0.64    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(forward_demodulation,[],[f627,f172])).
% 1.51/0.64  fof(f627,plain,(
% 1.51/0.64    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f626,f98])).
% 1.51/0.64  fof(f98,plain,(
% 1.51/0.64    v1_relat_1(sK2)),
% 1.51/0.64    inference(resolution,[],[f80,f60])).
% 1.51/0.64  fof(f80,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f37])).
% 1.51/0.64  fof(f37,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f9])).
% 1.51/0.64  fof(f9,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.51/0.64  fof(f626,plain,(
% 1.51/0.64    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f614,f58])).
% 1.51/0.64  fof(f614,plain,(
% 1.51/0.64    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(resolution,[],[f481,f68])).
% 1.51/0.64  fof(f68,plain,(
% 1.51/0.64    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f25])).
% 1.51/0.64  fof(f25,plain,(
% 1.51/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(flattening,[],[f24])).
% 1.51/0.64  fof(f24,plain,(
% 1.51/0.64    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.64    inference(ennf_transformation,[],[f6])).
% 1.51/0.64  fof(f6,axiom,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.51/0.64  fof(f481,plain,(
% 1.51/0.64    v2_funct_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(avatar_component_clause,[],[f479])).
% 1.51/0.64  fof(f1378,plain,(
% 1.51/0.64    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | spl3_33 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1377,f509])).
% 1.51/0.64  fof(f509,plain,(
% 1.51/0.64    sK2 != k6_relat_1(sK0) | spl3_33),
% 1.51/0.64    inference(avatar_component_clause,[],[f508])).
% 1.51/0.64  fof(f508,plain,(
% 1.51/0.64    spl3_33 <=> sK2 = k6_relat_1(sK0)),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.51/0.64  fof(f1377,plain,(
% 1.51/0.64    sK2 = k6_relat_1(sK0) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(forward_demodulation,[],[f1376,f172])).
% 1.51/0.64  fof(f1376,plain,(
% 1.51/0.64    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1375,f711])).
% 1.51/0.64  fof(f711,plain,(
% 1.51/0.64    v1_relat_1(k2_funct_1(sK2)) | ~spl3_44),
% 1.51/0.64    inference(avatar_component_clause,[],[f710])).
% 1.51/0.64  fof(f710,plain,(
% 1.51/0.64    spl3_44 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.51/0.64  fof(f1375,plain,(
% 1.51/0.64    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1374,f715])).
% 1.51/0.64  fof(f715,plain,(
% 1.51/0.64    v1_funct_1(k2_funct_1(sK2)) | ~spl3_45),
% 1.51/0.64    inference(avatar_component_clause,[],[f714])).
% 1.51/0.64  fof(f714,plain,(
% 1.51/0.64    spl3_45 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.51/0.64  fof(f1374,plain,(
% 1.51/0.64    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1373,f98])).
% 1.51/0.64  fof(f1373,plain,(
% 1.51/0.64    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1359,f58])).
% 1.51/0.64  fof(f1359,plain,(
% 1.51/0.64    sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(trivial_inequality_removal,[],[f1357])).
% 1.51/0.64  fof(f1357,plain,(
% 1.51/0.64    k2_funct_1(sK2) != k2_funct_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(superposition,[],[f72,f1350])).
% 1.51/0.64  fof(f1350,plain,(
% 1.51/0.64    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),sK2) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(forward_demodulation,[],[f1293,f1331])).
% 1.51/0.64  fof(f1331,plain,(
% 1.51/0.64    k6_relat_1(sK0) = k2_funct_1(sK2) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1330,f164])).
% 1.51/0.64  fof(f164,plain,(
% 1.51/0.64    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 1.51/0.64    inference(backward_demodulation,[],[f115,f159])).
% 1.51/0.64  fof(f159,plain,(
% 1.51/0.64    sK0 = k1_relat_1(sK1)),
% 1.51/0.64    inference(backward_demodulation,[],[f136,f156])).
% 1.51/0.64  fof(f156,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f155,f55])).
% 1.51/0.64  fof(f155,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f153,f56])).
% 1.51/0.64  fof(f153,plain,(
% 1.51/0.64    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.51/0.64    inference(resolution,[],[f76,f57])).
% 1.51/0.64  fof(f136,plain,(
% 1.51/0.64    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 1.51/0.64    inference(resolution,[],[f81,f57])).
% 1.51/0.64  fof(f115,plain,(
% 1.51/0.64    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 1.51/0.64    inference(subsumption_resolution,[],[f114,f97])).
% 1.51/0.64  fof(f97,plain,(
% 1.51/0.64    v1_relat_1(sK1)),
% 1.51/0.64    inference(resolution,[],[f80,f57])).
% 1.51/0.64  fof(f114,plain,(
% 1.51/0.64    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f113,f55])).
% 1.51/0.64  fof(f113,plain,(
% 1.51/0.64    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(resolution,[],[f68,f62])).
% 1.51/0.64  fof(f1330,plain,(
% 1.51/0.64    sK0 != k2_relat_1(k2_funct_1(sK1)) | k6_relat_1(sK0) = k2_funct_1(sK2) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(forward_demodulation,[],[f1292,f983])).
% 1.51/0.64  fof(f983,plain,(
% 1.51/0.64    sK0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(forward_demodulation,[],[f630,f648])).
% 1.51/0.64  fof(f648,plain,(
% 1.51/0.64    sK0 = k2_relat_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f647,f98])).
% 1.51/0.64  fof(f647,plain,(
% 1.51/0.64    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f645,f107])).
% 1.51/0.64  fof(f107,plain,(
% 1.51/0.64    v5_relat_1(sK2,sK0)),
% 1.51/0.64    inference(resolution,[],[f83,f60])).
% 1.51/0.64  fof(f83,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f39])).
% 1.51/0.64  fof(f39,plain,(
% 1.51/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.64    inference(ennf_transformation,[],[f10])).
% 1.51/0.64  fof(f10,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.51/0.64  fof(f645,plain,(
% 1.51/0.64    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.51/0.64    inference(resolution,[],[f608,f103])).
% 1.51/0.64  fof(f103,plain,(
% 1.51/0.64    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.51/0.64    inference(resolution,[],[f79,f74])).
% 1.51/0.64  fof(f74,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f51])).
% 1.51/0.64  fof(f51,plain,(
% 1.51/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(nnf_transformation,[],[f34])).
% 1.51/0.64  fof(f34,plain,(
% 1.51/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.51/0.64    inference(ennf_transformation,[],[f2])).
% 1.51/0.64  fof(f2,axiom,(
% 1.51/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.51/0.64  fof(f79,plain,(
% 1.51/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f53])).
% 1.51/0.64  fof(f53,plain,(
% 1.51/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.64    inference(flattening,[],[f52])).
% 1.51/0.64  fof(f52,plain,(
% 1.51/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.64    inference(nnf_transformation,[],[f1])).
% 1.51/0.64  fof(f1,axiom,(
% 1.51/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.64  fof(f608,plain,(
% 1.51/0.64    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.51/0.64    inference(forward_demodulation,[],[f607,f159])).
% 1.51/0.64  fof(f607,plain,(
% 1.51/0.64    r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))),
% 1.51/0.64    inference(subsumption_resolution,[],[f606,f97])).
% 1.51/0.64  fof(f606,plain,(
% 1.51/0.64    r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f605,f55])).
% 1.51/0.64  fof(f605,plain,(
% 1.51/0.64    r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f604,f98])).
% 1.51/0.64  fof(f604,plain,(
% 1.51/0.64    r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f603,f58])).
% 1.51/0.64  fof(f603,plain,(
% 1.51/0.64    r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(subsumption_resolution,[],[f591,f62])).
% 1.51/0.64  fof(f591,plain,(
% 1.51/0.64    ~v2_funct_1(sK1) | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(trivial_inequality_removal,[],[f590])).
% 1.51/0.64  fof(f590,plain,(
% 1.51/0.64    k2_relat_1(sK1) != k2_relat_1(sK1) | ~v2_funct_1(sK1) | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.51/0.64    inference(superposition,[],[f73,f567])).
% 1.51/0.64  fof(f73,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f33])).
% 1.51/0.64  fof(f33,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(flattening,[],[f32])).
% 1.51/0.64  fof(f32,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.64    inference(ennf_transformation,[],[f5])).
% 1.51/0.64  fof(f5,axiom,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
% 1.51/0.64  fof(f630,plain,(
% 1.51/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f629,f98])).
% 1.51/0.64  fof(f629,plain,(
% 1.51/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f615,f58])).
% 1.51/0.64  fof(f615,plain,(
% 1.51/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(resolution,[],[f481,f67])).
% 1.51/0.64  fof(f67,plain,(
% 1.51/0.64    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f25])).
% 1.51/0.64  fof(f1292,plain,(
% 1.51/0.64    k6_relat_1(sK0) = k2_funct_1(sK2) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(forward_demodulation,[],[f1291,f983])).
% 1.51/0.64  fof(f1291,plain,(
% 1.51/0.64    k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1290,f121])).
% 1.51/0.64  fof(f121,plain,(
% 1.51/0.64    v1_relat_1(k2_funct_1(sK1)) | ~spl3_1),
% 1.51/0.64    inference(avatar_component_clause,[],[f120])).
% 1.51/0.64  fof(f120,plain,(
% 1.51/0.64    spl3_1 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.51/0.64  fof(f1290,plain,(
% 1.51/0.64    k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_7 | ~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1289,f225])).
% 1.51/0.64  fof(f225,plain,(
% 1.51/0.64    v1_funct_1(k2_funct_1(sK1)) | ~spl3_7),
% 1.51/0.64    inference(avatar_component_clause,[],[f224])).
% 1.51/0.64  fof(f224,plain,(
% 1.51/0.64    spl3_7 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.51/0.64  fof(f1289,plain,(
% 1.51/0.64    k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_30 | ~spl3_44 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1288,f711])).
% 1.51/0.64  fof(f1288,plain,(
% 1.51/0.64    k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_30 | ~spl3_45)),
% 1.51/0.64    inference(subsumption_resolution,[],[f1287,f715])).
% 1.51/0.64  fof(f1287,plain,(
% 1.51/0.64    k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl3_30),
% 1.51/0.64    inference(trivial_inequality_removal,[],[f1285])).
% 1.51/0.64  fof(f1285,plain,(
% 1.51/0.64    k2_funct_1(sK1) != k2_funct_1(sK1) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_relat_1(k2_funct_1(sK1)) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl3_30),
% 1.51/0.64    inference(superposition,[],[f72,f618])).
% 1.51/0.64  fof(f618,plain,(
% 1.51/0.64    k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(forward_demodulation,[],[f617,f567])).
% 1.51/0.64  fof(f617,plain,(
% 1.51/0.64    k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f616,f98])).
% 1.51/0.64  fof(f616,plain,(
% 1.51/0.64    k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f610,f58])).
% 1.51/0.64  fof(f610,plain,(
% 1.51/0.64    k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(resolution,[],[f481,f175])).
% 1.51/0.64  fof(f175,plain,(
% 1.51/0.64    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(subsumption_resolution,[],[f174,f97])).
% 1.51/0.64  fof(f174,plain,(
% 1.51/0.64    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(subsumption_resolution,[],[f173,f55])).
% 1.51/0.64  fof(f173,plain,(
% 1.51/0.64    ( ! [X0] : (k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(resolution,[],[f71,f62])).
% 1.51/0.64  fof(f71,plain,(
% 1.51/0.64    ( ! [X0,X1] : (~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f29])).
% 1.51/0.64  fof(f29,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(flattening,[],[f28])).
% 1.51/0.64  fof(f28,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.64    inference(ennf_transformation,[],[f8])).
% 1.51/0.64  fof(f8,axiom,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 1.51/0.64  fof(f1293,plain,(
% 1.51/0.64    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK2),sK2) | ~spl3_30),
% 1.51/0.64    inference(forward_demodulation,[],[f622,f648])).
% 1.51/0.64  fof(f622,plain,(
% 1.51/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f621,f98])).
% 1.51/0.64  fof(f621,plain,(
% 1.51/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(subsumption_resolution,[],[f612,f58])).
% 1.51/0.64  fof(f612,plain,(
% 1.51/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_30),
% 1.51/0.64    inference(resolution,[],[f481,f70])).
% 1.51/0.64  fof(f70,plain,(
% 1.51/0.64    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f27])).
% 1.51/0.64  fof(f27,plain,(
% 1.51/0.64    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(flattening,[],[f26])).
% 1.51/0.64  fof(f26,plain,(
% 1.51/0.64    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.64    inference(ennf_transformation,[],[f7])).
% 1.51/0.64  fof(f7,axiom,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.51/0.64  fof(f72,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f31])).
% 1.51/0.64  fof(f31,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(flattening,[],[f30])).
% 1.51/0.64  fof(f30,plain,(
% 1.51/0.64    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.64    inference(ennf_transformation,[],[f4])).
% 1.51/0.64  fof(f4,axiom,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 1.51/0.64  fof(f863,plain,(
% 1.51/0.64    spl3_45),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f862])).
% 1.51/0.64  fof(f862,plain,(
% 1.51/0.64    $false | spl3_45),
% 1.51/0.64    inference(subsumption_resolution,[],[f861,f98])).
% 1.51/0.64  fof(f861,plain,(
% 1.51/0.64    ~v1_relat_1(sK2) | spl3_45),
% 1.51/0.64    inference(subsumption_resolution,[],[f860,f58])).
% 1.51/0.64  fof(f860,plain,(
% 1.51/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_45),
% 1.51/0.64    inference(resolution,[],[f716,f66])).
% 1.51/0.64  fof(f66,plain,(
% 1.51/0.64    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f23])).
% 1.51/0.64  fof(f23,plain,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(flattening,[],[f22])).
% 1.51/0.64  fof(f22,plain,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.64    inference(ennf_transformation,[],[f3])).
% 1.51/0.64  fof(f3,axiom,(
% 1.51/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.51/0.64  fof(f716,plain,(
% 1.51/0.64    ~v1_funct_1(k2_funct_1(sK2)) | spl3_45),
% 1.51/0.64    inference(avatar_component_clause,[],[f714])).
% 1.51/0.64  fof(f750,plain,(
% 1.51/0.64    spl3_44),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f749])).
% 1.51/0.64  fof(f749,plain,(
% 1.51/0.64    $false | spl3_44),
% 1.51/0.64    inference(subsumption_resolution,[],[f748,f98])).
% 1.51/0.64  fof(f748,plain,(
% 1.51/0.64    ~v1_relat_1(sK2) | spl3_44),
% 1.51/0.64    inference(subsumption_resolution,[],[f747,f58])).
% 1.51/0.64  fof(f747,plain,(
% 1.51/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_44),
% 1.51/0.64    inference(resolution,[],[f712,f65])).
% 1.51/0.64  fof(f65,plain,(
% 1.51/0.64    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f23])).
% 1.51/0.64  fof(f712,plain,(
% 1.51/0.64    ~v1_relat_1(k2_funct_1(sK2)) | spl3_44),
% 1.51/0.64    inference(avatar_component_clause,[],[f710])).
% 1.51/0.64  fof(f593,plain,(
% 1.51/0.64    spl3_32),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f592])).
% 1.51/0.64  fof(f592,plain,(
% 1.51/0.64    $false | spl3_32),
% 1.51/0.64    inference(subsumption_resolution,[],[f588,f62])).
% 1.51/0.64  fof(f588,plain,(
% 1.51/0.64    ~v2_funct_1(sK1) | spl3_32),
% 1.51/0.64    inference(backward_demodulation,[],[f489,f567])).
% 1.51/0.64  fof(f489,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | spl3_32),
% 1.51/0.64    inference(avatar_component_clause,[],[f487])).
% 1.51/0.64  fof(f487,plain,(
% 1.51/0.64    spl3_32 <=> v2_funct_1(k5_relat_1(sK2,sK1))),
% 1.51/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.51/0.64  fof(f523,plain,(
% 1.51/0.64    ~spl3_33),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f522])).
% 1.51/0.64  fof(f522,plain,(
% 1.51/0.64    $false | ~spl3_33),
% 1.51/0.64    inference(subsumption_resolution,[],[f520,f109])).
% 1.51/0.64  fof(f109,plain,(
% 1.51/0.64    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.51/0.64    inference(resolution,[],[f96,f60])).
% 1.51/0.64  fof(f96,plain,(
% 1.51/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.51/0.64    inference(duplicate_literal_removal,[],[f95])).
% 1.51/0.64  fof(f95,plain,(
% 1.51/0.64    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(equality_resolution,[],[f87])).
% 1.51/0.64  fof(f87,plain,(
% 1.51/0.64    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f54])).
% 1.51/0.64  fof(f520,plain,(
% 1.51/0.64    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_33),
% 1.51/0.64    inference(backward_demodulation,[],[f91,f510])).
% 1.51/0.64  fof(f510,plain,(
% 1.51/0.64    sK2 = k6_relat_1(sK0) | ~spl3_33),
% 1.51/0.64    inference(avatar_component_clause,[],[f508])).
% 1.51/0.64  fof(f91,plain,(
% 1.51/0.64    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.51/0.64    inference(definition_unfolding,[],[f63,f64])).
% 1.51/0.64  fof(f64,plain,(
% 1.51/0.64    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f15])).
% 1.51/0.64  fof(f15,axiom,(
% 1.51/0.64    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.51/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.51/0.64  fof(f63,plain,(
% 1.51/0.64    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.51/0.64    inference(cnf_transformation,[],[f50])).
% 1.51/0.64  fof(f490,plain,(
% 1.51/0.64    spl3_30 | spl3_31 | ~spl3_32),
% 1.51/0.64    inference(avatar_split_clause,[],[f477,f487,f483,f479])).
% 1.51/0.64  fof(f477,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f476,f58])).
% 1.51/0.64  fof(f476,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f475,f59])).
% 1.51/0.64  fof(f475,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f474,f60])).
% 1.51/0.64  fof(f474,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f473,f55])).
% 1.51/0.64  fof(f473,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f472,f56])).
% 1.51/0.64  fof(f472,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(subsumption_resolution,[],[f451,f57])).
% 1.51/0.64  fof(f451,plain,(
% 1.51/0.64    ~v2_funct_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 1.51/0.64    inference(superposition,[],[f84,f376])).
% 1.51/0.64  fof(f84,plain,(
% 1.51/0.64    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f41])).
% 1.51/0.64  fof(f245,plain,(
% 1.51/0.64    spl3_7),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f244])).
% 1.51/0.64  fof(f244,plain,(
% 1.51/0.64    $false | spl3_7),
% 1.51/0.64    inference(subsumption_resolution,[],[f243,f97])).
% 1.51/0.64  fof(f243,plain,(
% 1.51/0.64    ~v1_relat_1(sK1) | spl3_7),
% 1.51/0.64    inference(subsumption_resolution,[],[f242,f55])).
% 1.51/0.64  fof(f242,plain,(
% 1.51/0.64    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_7),
% 1.51/0.64    inference(resolution,[],[f226,f66])).
% 1.51/0.64  fof(f226,plain,(
% 1.51/0.64    ~v1_funct_1(k2_funct_1(sK1)) | spl3_7),
% 1.51/0.64    inference(avatar_component_clause,[],[f224])).
% 1.51/0.64  fof(f141,plain,(
% 1.51/0.64    spl3_1),
% 1.51/0.64    inference(avatar_contradiction_clause,[],[f140])).
% 1.51/0.64  fof(f140,plain,(
% 1.51/0.64    $false | spl3_1),
% 1.51/0.64    inference(subsumption_resolution,[],[f139,f97])).
% 1.51/0.64  fof(f139,plain,(
% 1.51/0.64    ~v1_relat_1(sK1) | spl3_1),
% 1.51/0.64    inference(subsumption_resolution,[],[f138,f55])).
% 1.51/0.64  fof(f138,plain,(
% 1.51/0.64    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_1),
% 1.51/0.64    inference(resolution,[],[f122,f65])).
% 1.51/0.64  fof(f122,plain,(
% 1.51/0.64    ~v1_relat_1(k2_funct_1(sK1)) | spl3_1),
% 1.51/0.64    inference(avatar_component_clause,[],[f120])).
% 1.51/0.64  % SZS output end Proof for theBenchmark
% 1.51/0.64  % (27288)------------------------------
% 1.51/0.64  % (27288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.64  % (27288)Termination reason: Refutation
% 1.51/0.64  
% 1.51/0.64  % (27288)Memory used [KB]: 11385
% 1.51/0.64  % (27288)Time elapsed: 0.194 s
% 1.51/0.64  % (27288)------------------------------
% 1.51/0.64  % (27288)------------------------------
% 1.51/0.65  % (27281)Success in time 0.28 s
%------------------------------------------------------------------------------
