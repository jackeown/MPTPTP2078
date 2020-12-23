%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 607 expanded)
%              Number of leaves         :   27 ( 190 expanded)
%              Depth                    :   17
%              Number of atoms          :  430 (2777 expanded)
%              Number of equality atoms :  105 ( 727 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f962,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f222,f285,f301,f464,f607,f679,f699,f739,f751,f891,f907,f954])).

fof(f954,plain,(
    ~ spl5_69 ),
    inference(avatar_contradiction_clause,[],[f949])).

fof(f949,plain,
    ( $false
    | ~ spl5_69 ),
    inference(resolution,[],[f926,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f926,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_69 ),
    inference(resolution,[],[f906,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f906,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f905])).

fof(f905,plain,
    ( spl5_69
  <=> r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f907,plain,
    ( spl5_8
    | spl5_69
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f901,f887,f905,f155])).

fof(f155,plain,
    ( spl5_8
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f887,plain,
    ( spl5_68
  <=> k1_xboole_0 = sK4(k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f901,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl5_68 ),
    inference(superposition,[],[f69,f888])).

fof(f888,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f887])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f891,plain,
    ( ~ spl5_6
    | ~ spl5_12
    | spl5_68
    | ~ spl5_2
    | spl5_61 ),
    inference(avatar_split_clause,[],[f890,f695,f108,f887,f185,f137])).

fof(f137,plain,
    ( spl5_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f185,plain,
    ( spl5_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f108,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f695,plain,
    ( spl5_61
  <=> r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f890,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_2
    | spl5_61 ),
    inference(forward_demodulation,[],[f883,f728])).

fof(f728,plain,
    ( sK4(k1_xboole_0,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(k1_xboole_0,k2_relat_1(sK2))))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f394,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f394,plain,(
    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))) ),
    inference(global_subsumption,[],[f387])).

% (15357)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f387,plain,(
    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))) ),
    inference(global_subsumption,[],[f336])).

fof(f336,plain,(
    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f318,f114])).

fof(f114,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | sK4(sK1,X3) = k1_funct_1(sK2,sK3(sK4(sK1,X3))) ) ),
    inference(resolution,[],[f52,f69])).

fof(f52,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f318,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(global_subsumption,[],[f315,f317])).

fof(f317,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f126,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f126,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(global_subsumption,[],[f102,f125])).

fof(f125,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f99,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f50,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f315,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f53,f101])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f50,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f53,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f883,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK3(sK4(k1_xboole_0,k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_2
    | spl5_61 ),
    inference(resolution,[],[f865,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f865,plain,
    ( ~ r2_hidden(sK3(sK4(k1_xboole_0,k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl5_2
    | spl5_61 ),
    inference(forward_demodulation,[],[f696,f109])).

fof(f696,plain,
    ( ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))
    | spl5_61 ),
    inference(avatar_component_clause,[],[f695])).

fof(f751,plain,
    ( ~ spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f750,f140,f158,f155])).

fof(f158,plain,
    ( spl5_9
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f140,plain,
    ( spl5_7
  <=> r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f750,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl5_7 ),
    inference(resolution,[],[f141,f67])).

fof(f141,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f739,plain,
    ( ~ spl5_6
    | spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f738,f108,f140,f137])).

fof(f738,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f705,f62])).

fof(f705,plain,
    ( v5_relat_1(sK2,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f99,f109])).

fof(f699,plain,
    ( ~ spl5_61
    | spl5_38 ),
    inference(avatar_split_clause,[],[f698,f459,f695])).

fof(f459,plain,
    ( spl5_38
  <=> r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f698,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(global_subsumption,[],[f102,f48,f455])).

fof(f455,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f64,f394])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f679,plain,(
    ~ spl5_38 ),
    inference(avatar_contradiction_clause,[],[f676])).

fof(f676,plain,
    ( $false
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f318,f646])).

fof(f646,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_38 ),
    inference(resolution,[],[f460,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f460,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f459])).

fof(f607,plain,(
    spl5_39 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | spl5_39 ),
    inference(subsumption_resolution,[],[f318,f584])).

fof(f584,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | spl5_39 ),
    inference(resolution,[],[f576,f69])).

fof(f576,plain,
    ( ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | spl5_39 ),
    inference(resolution,[],[f463,f51])).

fof(f51,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f463,plain,
    ( ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f462])).

% (15344)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f462,plain,
    ( spl5_39
  <=> r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f464,plain,
    ( ~ spl5_6
    | ~ spl5_12
    | spl5_38
    | ~ spl5_39
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f457,f105,f462,f459,f185,f137])).

fof(f105,plain,
    ( spl5_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f457,plain,
    ( ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f455,f310])).

fof(f310,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f100,f106])).

fof(f106,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f100,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f50,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f301,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f300,f108,f105])).

fof(f300,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f49,f294])).

fof(f294,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f50,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f285,plain,
    ( ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f261,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f261,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f241,f252])).

fof(f252,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f101,f109])).

fof(f241,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f53,f109])).

fof(f222,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f48,f186])).

fof(f186,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f145,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f102,f138])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:59:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (15369)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.50  % (15358)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (15354)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (15353)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (15361)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (15346)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (15361)Refutation not found, incomplete strategy% (15361)------------------------------
% 0.22/0.51  % (15361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15361)Memory used [KB]: 10618
% 0.22/0.51  % (15361)Time elapsed: 0.100 s
% 0.22/0.51  % (15361)------------------------------
% 0.22/0.51  % (15361)------------------------------
% 0.22/0.52  % (15362)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (15354)Refutation not found, incomplete strategy% (15354)------------------------------
% 0.22/0.52  % (15354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15354)Memory used [KB]: 10746
% 0.22/0.52  % (15354)Time elapsed: 0.104 s
% 0.22/0.52  % (15354)------------------------------
% 0.22/0.52  % (15354)------------------------------
% 0.22/0.52  % (15350)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (15347)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (15352)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (15364)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (15363)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (15370)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (15356)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (15345)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (15365)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (15367)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (15355)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (15368)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (15355)Refutation not found, incomplete strategy% (15355)------------------------------
% 0.22/0.53  % (15355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15355)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15355)Memory used [KB]: 10746
% 0.22/0.53  % (15355)Time elapsed: 0.124 s
% 0.22/0.53  % (15355)------------------------------
% 0.22/0.53  % (15355)------------------------------
% 0.22/0.53  % (15359)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (15373)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (15372)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (15348)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (15349)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (15371)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (15360)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (15366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (15351)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (15346)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f962,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f145,f222,f285,f301,f464,f607,f679,f699,f739,f751,f891,f907,f954])).
% 0.22/0.55  fof(f954,plain,(
% 0.22/0.55    ~spl5_69),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f949])).
% 0.22/0.55  fof(f949,plain,(
% 0.22/0.55    $false | ~spl5_69),
% 0.22/0.55    inference(resolution,[],[f926,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f926,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_69),
% 0.22/0.55    inference(resolution,[],[f906,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.55  fof(f906,plain,(
% 0.22/0.55    r2_hidden(k1_xboole_0,k1_xboole_0) | ~spl5_69),
% 0.22/0.55    inference(avatar_component_clause,[],[f905])).
% 0.22/0.55  fof(f905,plain,(
% 0.22/0.55    spl5_69 <=> r2_hidden(k1_xboole_0,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 0.22/0.55  fof(f907,plain,(
% 0.22/0.55    spl5_8 | spl5_69 | ~spl5_68),
% 0.22/0.55    inference(avatar_split_clause,[],[f901,f887,f905,f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    spl5_8 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.55  fof(f887,plain,(
% 0.22/0.55    spl5_68 <=> k1_xboole_0 = sK4(k1_xboole_0,k2_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.22/0.55  fof(f901,plain,(
% 0.22/0.55    r2_hidden(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | ~spl5_68),
% 0.22/0.55    inference(superposition,[],[f69,f888])).
% 0.22/0.55  fof(f888,plain,(
% 0.22/0.55    k1_xboole_0 = sK4(k1_xboole_0,k2_relat_1(sK2)) | ~spl5_68),
% 0.22/0.55    inference(avatar_component_clause,[],[f887])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f891,plain,(
% 0.22/0.55    ~spl5_6 | ~spl5_12 | spl5_68 | ~spl5_2 | spl5_61),
% 0.22/0.55    inference(avatar_split_clause,[],[f890,f695,f108,f887,f185,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl5_6 <=> v1_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    spl5_12 <=> v1_funct_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    spl5_2 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.55  fof(f695,plain,(
% 0.22/0.55    spl5_61 <=> r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.22/0.55  fof(f890,plain,(
% 0.22/0.55    k1_xboole_0 = sK4(k1_xboole_0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_2 | spl5_61)),
% 0.22/0.55    inference(forward_demodulation,[],[f883,f728])).
% 0.22/0.55  fof(f728,plain,(
% 0.22/0.55    sK4(k1_xboole_0,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(k1_xboole_0,k2_relat_1(sK2)))) | ~spl5_2),
% 0.22/0.55    inference(backward_demodulation,[],[f394,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl5_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f108])).
% 0.22/0.55  fof(f394,plain,(
% 0.22/0.55    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2))))),
% 0.22/0.55    inference(global_subsumption,[],[f387])).
% 0.22/0.55  % (15357)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  fof(f387,plain,(
% 0.22/0.55    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2))))),
% 0.22/0.55    inference(global_subsumption,[],[f336])).
% 0.22/0.55  fof(f336,plain,(
% 0.22/0.55    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2))))),
% 0.22/0.55    inference(resolution,[],[f318,f114])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ( ! [X3] : (r1_tarski(sK1,X3) | sK4(sK1,X3) = k1_funct_1(sK2,sK3(sK4(sK1,X3)))) )),
% 0.22/0.55    inference(resolution,[],[f52,f69])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f35,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.55  fof(f318,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.55    inference(global_subsumption,[],[f315,f317])).
% 0.22/0.55  fof(f317,plain,(
% 0.22/0.55    sK1 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f126,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.55    inference(global_subsumption,[],[f102,f125])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f99,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    v5_relat_1(sK2,sK1)),
% 0.22/0.55    inference(resolution,[],[f50,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f50,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f315,plain,(
% 0.22/0.55    sK1 != k2_relat_1(sK2)),
% 0.22/0.55    inference(superposition,[],[f53,f101])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f50,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f883,plain,(
% 0.22/0.55    k1_xboole_0 = k1_funct_1(sK2,sK3(sK4(k1_xboole_0,k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_2 | spl5_61)),
% 0.22/0.55    inference(resolution,[],[f865,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.55  fof(f865,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK4(k1_xboole_0,k2_relat_1(sK2))),k1_relat_1(sK2)) | (~spl5_2 | spl5_61)),
% 0.22/0.55    inference(forward_demodulation,[],[f696,f109])).
% 0.22/0.55  fof(f696,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) | spl5_61),
% 0.22/0.55    inference(avatar_component_clause,[],[f695])).
% 0.22/0.55  fof(f751,plain,(
% 0.22/0.55    ~spl5_8 | spl5_9 | ~spl5_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f750,f140,f158,f155])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    spl5_9 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    spl5_7 <=> r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.55  fof(f750,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(sK2) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | ~spl5_7),
% 0.22/0.55    inference(resolution,[],[f141,f67])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),k1_xboole_0) | ~spl5_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f140])).
% 0.22/0.55  fof(f739,plain,(
% 0.22/0.55    ~spl5_6 | spl5_7 | ~spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f738,f108,f140,f137])).
% 0.22/0.55  fof(f738,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | ~spl5_2),
% 0.22/0.55    inference(resolution,[],[f705,f62])).
% 0.22/0.55  fof(f705,plain,(
% 0.22/0.55    v5_relat_1(sK2,k1_xboole_0) | ~spl5_2),
% 0.22/0.55    inference(backward_demodulation,[],[f99,f109])).
% 0.22/0.55  fof(f699,plain,(
% 0.22/0.55    ~spl5_61 | spl5_38),
% 0.22/0.55    inference(avatar_split_clause,[],[f698,f459,f695])).
% 0.22/0.55  fof(f459,plain,(
% 0.22/0.55    spl5_38 <=> r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.22/0.55  fof(f698,plain,(
% 0.22/0.55    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))),
% 0.22/0.55    inference(global_subsumption,[],[f102,f48,f455])).
% 0.22/0.55  fof(f455,plain,(
% 0.22/0.55    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.55    inference(superposition,[],[f64,f394])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f679,plain,(
% 0.22/0.55    ~spl5_38),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f676])).
% 0.22/0.55  fof(f676,plain,(
% 0.22/0.55    $false | ~spl5_38),
% 0.22/0.55    inference(subsumption_resolution,[],[f318,f646])).
% 0.22/0.55  fof(f646,plain,(
% 0.22/0.55    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_38),
% 0.22/0.55    inference(resolution,[],[f460,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f460,plain,(
% 0.22/0.55    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl5_38),
% 0.22/0.55    inference(avatar_component_clause,[],[f459])).
% 0.22/0.55  fof(f607,plain,(
% 0.22/0.55    spl5_39),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f604])).
% 0.22/0.55  fof(f604,plain,(
% 0.22/0.55    $false | spl5_39),
% 0.22/0.55    inference(subsumption_resolution,[],[f318,f584])).
% 0.22/0.55  fof(f584,plain,(
% 0.22/0.55    r1_tarski(sK1,k2_relat_1(sK2)) | spl5_39),
% 0.22/0.55    inference(resolution,[],[f576,f69])).
% 0.22/0.55  fof(f576,plain,(
% 0.22/0.55    ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | spl5_39),
% 0.22/0.55    inference(resolution,[],[f463,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f463,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | spl5_39),
% 0.22/0.55    inference(avatar_component_clause,[],[f462])).
% 0.22/0.55  % (15344)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  fof(f462,plain,(
% 0.22/0.55    spl5_39 <=> r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.22/0.55  fof(f464,plain,(
% 0.22/0.55    ~spl5_6 | ~spl5_12 | spl5_38 | ~spl5_39 | ~spl5_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f457,f105,f462,f459,f185,f137])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    spl5_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.55  fof(f457,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_1),
% 0.22/0.55    inference(forward_demodulation,[],[f455,f310])).
% 0.22/0.55  fof(f310,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | ~spl5_1),
% 0.22/0.55    inference(forward_demodulation,[],[f100,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f105])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f50,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f301,plain,(
% 0.22/0.55    spl5_1 | spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f300,f108,f105])).
% 0.22/0.55  fof(f300,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(global_subsumption,[],[f49,f294])).
% 0.22/0.55  fof(f294,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(resolution,[],[f50,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    ~spl5_2 | ~spl5_9),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f280])).
% 0.22/0.55  fof(f280,plain,(
% 0.22/0.55    $false | (~spl5_2 | ~spl5_9)),
% 0.22/0.55    inference(subsumption_resolution,[],[f261,f159])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f158])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    k1_xboole_0 != k2_relat_1(sK2) | ~spl5_2),
% 0.22/0.55    inference(superposition,[],[f241,f252])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl5_2),
% 0.22/0.55    inference(forward_demodulation,[],[f101,f109])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl5_2),
% 0.22/0.55    inference(backward_demodulation,[],[f53,f109])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    spl5_12),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f221])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    $false | spl5_12),
% 0.22/0.55    inference(subsumption_resolution,[],[f48,f186])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | spl5_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f185])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    spl5_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f144])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    $false | spl5_6),
% 0.22/0.55    inference(subsumption_resolution,[],[f102,f138])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | spl5_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f137])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (15346)------------------------------
% 0.22/0.55  % (15346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15346)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (15346)Memory used [KB]: 11385
% 0.22/0.55  % (15346)Time elapsed: 0.125 s
% 0.22/0.55  % (15346)------------------------------
% 0.22/0.55  % (15346)------------------------------
% 0.22/0.55  % (15344)Refutation not found, incomplete strategy% (15344)------------------------------
% 0.22/0.55  % (15344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15344)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15344)Memory used [KB]: 1791
% 0.22/0.55  % (15344)Time elapsed: 0.117 s
% 0.22/0.55  % (15344)------------------------------
% 0.22/0.55  % (15344)------------------------------
% 0.22/0.56  % (15343)Success in time 0.186 s
%------------------------------------------------------------------------------
