%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:33 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  128 (1111 expanded)
%              Number of leaves         :   26 ( 373 expanded)
%              Depth                    :   21
%              Number of atoms          :  521 (9008 expanded)
%              Number of equality atoms :   78 (2711 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f152,f229,f1161])).

fof(f1161,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f1160])).

fof(f1160,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f1146,f414])).

fof(f414,plain,
    ( ~ sP9(sK0)
    | ~ spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f304,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f99,f117_D])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f117_D])).

fof(f117_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f304,plain,
    ( r2_hidden(sK5(sK0,sK1,sK2),sK0)
    | ~ spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f126,f213])).

fof(f213,plain,
    ( ! [X8] :
        ( v1_funct_2(sK2,sK0,X8)
        | r2_hidden(sK5(sK0,X8,sK2),sK0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f212,f151])).

fof(f151,plain,(
    v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f132,f134])).

fof(f134,plain,(
    sK2 = sK8(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f57,f114])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
              & k1_relat_1(sK7(X0,X1,X2)) = X0
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
                & k1_relat_1(sK8(X0,X1,X6)) = X0
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK6(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
        & k1_relat_1(sK7(X0,X1,X2)) = X0
        & sK6(X0,X1,X2) = sK7(X0,X1,X2)
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
        & k1_relat_1(sK8(X0,X1,X6)) = X0
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f57,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f132,plain,(
    v1_relat_1(sK8(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f116])).

fof(f116,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f212,plain,
    ( ! [X8] :
        ( r2_hidden(sK5(sK0,X8,sK2),sK0)
        | v1_funct_2(sK2,sK0,X8)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f199,f121])).

fof(f121,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl10_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f199,plain,(
    ! [X8] :
      ( r2_hidden(sK5(sK0,X8,sK2),sK0)
      | v1_funct_2(sK2,sK0,X8)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f105,f146])).

fof(f146,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f135,f134])).

fof(f135,plain,(
    sK0 = k1_relat_1(sK8(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f113])).

fof(f113,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f126,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1146,plain,
    ( sP9(sK0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f278,f1033,f117])).

fof(f1033,plain,
    ( ! [X0] : m1_subset_1(sK0,k1_zfmisc_1(X0))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f1025,f1032])).

fof(f1032,plain,
    ( ! [X0,X1] : sK0 = k1_relset_1(X0,X1,sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f1026,f146])).

fof(f1026,plain,
    ( ! [X0,X1] : k1_relat_1(sK2) = k1_relset_1(X0,X1,sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f602,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f602,plain,
    ( ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f360,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f360,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f310,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f310,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f278,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
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

fof(f1025,plain,
    ( ! [X0,X1] : m1_subset_1(k1_relset_1(X0,X1,sK2),k1_zfmisc_1(X0))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f602,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f278,plain,
    ( v1_xboole_0(sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f163,f271,f66])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f271,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f121,f231,f168,f163,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f168,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f153,f146])).

fof(f153,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f121,f151,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f231,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f121,f126,f129,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f163,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f158,f146])).

fof(f158,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f100,f100,f151,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f229,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f228,f128])).

fof(f228,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f219,f146])).

fof(f219,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f151,f101,f147,f75])).

fof(f147,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f136,f134])).

fof(f136,plain,(
    r1_tarski(k2_relat_1(sK8(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f57,f112])).

fof(f112,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f152,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f148,f120])).

fof(f148,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f133,f134])).

fof(f133,plain,(
    v1_funct_1(sK8(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f115])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f131,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f58,f128,f124,f120])).

fof(f58,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.50/0.57  % (14058)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.57  % (14045)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.58  % (14042)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.58  % (14044)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.58  % (14040)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.58  % (14035)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.58  % (14052)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.58  % (14053)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.58  % (14037)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.58  % (14038)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.59  % (14033)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.60  % (14030)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.60  % (14032)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.60  % (14048)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.60  % (14060)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.61  % (14049)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.61  % (14034)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.61  % (14056)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.61  % (14047)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.62  % (14041)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.62  % (14054)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.62  % (14059)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.63  % (14051)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.63  % (14055)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.63  % (14046)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.63  % (14061)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.64  % (14043)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.64  % (14039)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.64  % (14036)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.66  % (14031)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.24/0.68  % (14058)Refutation found. Thanks to Tanya!
% 2.24/0.68  % SZS status Theorem for theBenchmark
% 2.58/0.70  % SZS output start Proof for theBenchmark
% 2.58/0.70  fof(f1162,plain,(
% 2.58/0.70    $false),
% 2.58/0.70    inference(avatar_sat_refutation,[],[f131,f152,f229,f1161])).
% 2.58/0.70  fof(f1161,plain,(
% 2.58/0.70    ~spl10_1 | spl10_2 | ~spl10_3),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f1160])).
% 2.58/0.70  fof(f1160,plain,(
% 2.58/0.70    $false | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1146,f414])).
% 2.58/0.70  fof(f414,plain,(
% 2.58/0.70    ~sP9(sK0) | (~spl10_1 | spl10_2)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f304,f118])).
% 2.58/0.70  fof(f118,plain,(
% 2.58/0.70    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 2.58/0.70    inference(general_splitting,[],[f99,f117_D])).
% 2.58/0.70  fof(f117,plain,(
% 2.58/0.70    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP9(X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f117_D])).
% 2.58/0.70  fof(f117_D,plain,(
% 2.58/0.70    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP9(X1)) )),
% 2.58/0.70    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 2.58/0.70  fof(f99,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f35])).
% 2.58/0.70  fof(f35,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.58/0.70    inference(ennf_transformation,[],[f6])).
% 2.58/0.70  fof(f6,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.58/0.70  fof(f304,plain,(
% 2.58/0.70    r2_hidden(sK5(sK0,sK1,sK2),sK0) | (~spl10_1 | spl10_2)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f126,f213])).
% 2.58/0.70  fof(f213,plain,(
% 2.58/0.70    ( ! [X8] : (v1_funct_2(sK2,sK0,X8) | r2_hidden(sK5(sK0,X8,sK2),sK0)) ) | ~spl10_1),
% 2.58/0.70    inference(subsumption_resolution,[],[f212,f151])).
% 2.58/0.70  fof(f151,plain,(
% 2.58/0.70    v1_relat_1(sK2)),
% 2.58/0.70    inference(forward_demodulation,[],[f132,f134])).
% 2.58/0.70  fof(f134,plain,(
% 2.58/0.70    sK2 = sK8(sK0,sK1,sK2)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f57,f114])).
% 2.58/0.70  fof(f114,plain,(
% 2.58/0.70    ( ! [X6,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.58/0.70    inference(equality_resolution,[],[f89])).
% 2.58/0.70  fof(f89,plain,(
% 2.58/0.70    ( ! [X6,X2,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.58/0.70    inference(cnf_transformation,[],[f56])).
% 2.58/0.70  fof(f56,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1) & k1_relat_1(sK7(X0,X1,X2)) = X0 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) & k1_relat_1(sK8(X0,X1,X6)) = X0 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 2.58/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f55,f54,f53])).
% 2.58/0.70  fof(f53,plain,(
% 2.58/0.70    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f54,plain,(
% 2.58/0.70    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1) & k1_relat_1(sK7(X0,X1,X2)) = X0 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f55,plain,(
% 2.58/0.70    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) & k1_relat_1(sK8(X0,X1,X6)) = X0 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f52,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 2.58/0.70    inference(rectify,[],[f51])).
% 2.58/0.70  fof(f51,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 2.58/0.70    inference(nnf_transformation,[],[f13])).
% 2.58/0.70  fof(f13,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 2.58/0.70  fof(f57,plain,(
% 2.58/0.70    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 2.58/0.70    inference(cnf_transformation,[],[f37])).
% 2.58/0.70  fof(f37,plain,(
% 2.58/0.70    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 2.58/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f36])).
% 2.58/0.70  fof(f36,plain,(
% 2.58/0.70    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f18,plain,(
% 2.58/0.70    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.58/0.70    inference(ennf_transformation,[],[f17])).
% 2.58/0.70  fof(f17,negated_conjecture,(
% 2.58/0.70    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.58/0.70    inference(negated_conjecture,[],[f16])).
% 2.58/0.70  fof(f16,conjecture,(
% 2.58/0.70    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 2.58/0.70  fof(f132,plain,(
% 2.58/0.70    v1_relat_1(sK8(sK0,sK1,sK2))),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f57,f116])).
% 2.58/0.70  fof(f116,plain,(
% 2.58/0.70    ( ! [X6,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.58/0.70    inference(equality_resolution,[],[f87])).
% 2.58/0.70  fof(f87,plain,(
% 2.58/0.70    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.58/0.70    inference(cnf_transformation,[],[f56])).
% 2.58/0.70  fof(f212,plain,(
% 2.58/0.70    ( ! [X8] : (r2_hidden(sK5(sK0,X8,sK2),sK0) | v1_funct_2(sK2,sK0,X8) | ~v1_relat_1(sK2)) ) | ~spl10_1),
% 2.58/0.70    inference(subsumption_resolution,[],[f199,f121])).
% 2.58/0.70  fof(f121,plain,(
% 2.58/0.70    v1_funct_1(sK2) | ~spl10_1),
% 2.58/0.70    inference(avatar_component_clause,[],[f120])).
% 2.58/0.70  fof(f120,plain,(
% 2.58/0.70    spl10_1 <=> v1_funct_1(sK2)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.58/0.70  fof(f199,plain,(
% 2.58/0.70    ( ! [X8] : (r2_hidden(sK5(sK0,X8,sK2),sK0) | v1_funct_2(sK2,sK0,X8) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.58/0.70    inference(superposition,[],[f105,f146])).
% 2.58/0.70  fof(f146,plain,(
% 2.58/0.70    sK0 = k1_relat_1(sK2)),
% 2.58/0.70    inference(backward_demodulation,[],[f135,f134])).
% 2.58/0.70  fof(f135,plain,(
% 2.58/0.70    sK0 = k1_relat_1(sK8(sK0,sK1,sK2))),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f57,f113])).
% 2.58/0.70  fof(f113,plain,(
% 2.58/0.70    ( ! [X6,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X0 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.58/0.70    inference(equality_resolution,[],[f90])).
% 2.58/0.70  fof(f90,plain,(
% 2.58/0.70    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.58/0.70    inference(cnf_transformation,[],[f56])).
% 2.58/0.70  fof(f105,plain,(
% 2.58/0.70    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.58/0.70    inference(equality_resolution,[],[f82])).
% 2.58/0.70  fof(f82,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK5(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f50])).
% 2.58/0.70  fof(f50,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.58/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f49])).
% 2.58/0.70  fof(f49,plain,(
% 2.58/0.70    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f32,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.58/0.70    inference(flattening,[],[f31])).
% 2.58/0.70  fof(f31,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.58/0.70    inference(ennf_transformation,[],[f15])).
% 2.58/0.70  fof(f15,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 2.58/0.70  fof(f126,plain,(
% 2.58/0.70    ~v1_funct_2(sK2,sK0,sK1) | spl10_2),
% 2.58/0.70    inference(avatar_component_clause,[],[f124])).
% 2.58/0.70  fof(f124,plain,(
% 2.58/0.70    spl10_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.58/0.70  fof(f1146,plain,(
% 2.58/0.70    sP9(sK0) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f278,f1033,f117])).
% 2.58/0.70  fof(f1033,plain,(
% 2.58/0.70    ( ! [X0] : (m1_subset_1(sK0,k1_zfmisc_1(X0))) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(forward_demodulation,[],[f1025,f1032])).
% 2.58/0.70  fof(f1032,plain,(
% 2.58/0.70    ( ! [X0,X1] : (sK0 = k1_relset_1(X0,X1,sK2)) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(forward_demodulation,[],[f1026,f146])).
% 2.58/0.70  fof(f1026,plain,(
% 2.58/0.70    ( ! [X0,X1] : (k1_relat_1(sK2) = k1_relset_1(X0,X1,sK2)) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f602,f76])).
% 2.58/0.70  fof(f76,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f27])).
% 2.58/0.70  fof(f27,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(ennf_transformation,[],[f9])).
% 2.58/0.70  fof(f9,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.58/0.70  fof(f602,plain,(
% 2.58/0.70    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f360,f74])).
% 2.58/0.70  fof(f74,plain,(
% 2.58/0.70    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f48])).
% 2.58/0.70  fof(f48,plain,(
% 2.58/0.70    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.58/0.70    inference(nnf_transformation,[],[f5])).
% 2.58/0.70  fof(f5,axiom,(
% 2.58/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.58/0.70  fof(f360,plain,(
% 2.58/0.70    ( ! [X0] : (r1_tarski(sK2,X0)) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f310,f71])).
% 2.58/0.70  fof(f71,plain,(
% 2.58/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f47])).
% 2.58/0.70  fof(f47,plain,(
% 2.58/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.58/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 2.58/0.70  fof(f46,plain,(
% 2.58/0.70    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f45,plain,(
% 2.58/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.58/0.70    inference(rectify,[],[f44])).
% 2.58/0.70  fof(f44,plain,(
% 2.58/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.58/0.70    inference(nnf_transformation,[],[f24])).
% 2.58/0.70  fof(f24,plain,(
% 2.58/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f2])).
% 2.58/0.70  fof(f2,axiom,(
% 2.58/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.58/0.70  fof(f310,plain,(
% 2.58/0.70    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f278,f62])).
% 2.58/0.70  fof(f62,plain,(
% 2.58/0.70    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f41])).
% 2.58/0.70  fof(f41,plain,(
% 2.58/0.70    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.58/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.58/0.70  fof(f40,plain,(
% 2.58/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f39,plain,(
% 2.58/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.58/0.70    inference(rectify,[],[f38])).
% 2.58/0.70  fof(f38,plain,(
% 2.58/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.58/0.70    inference(nnf_transformation,[],[f1])).
% 2.58/0.70  fof(f1,axiom,(
% 2.58/0.70    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.58/0.70  fof(f1025,plain,(
% 2.58/0.70    ( ! [X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,sK2),k1_zfmisc_1(X0))) ) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f602,f77])).
% 2.58/0.70  fof(f77,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f28])).
% 2.58/0.70  fof(f28,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(ennf_transformation,[],[f8])).
% 2.58/0.70  fof(f8,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 2.58/0.70  fof(f278,plain,(
% 2.58/0.70    v1_xboole_0(sK2) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f163,f271,f66])).
% 2.58/0.70  fof(f66,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f23])).
% 2.58/0.70  fof(f23,plain,(
% 2.58/0.70    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.58/0.70    inference(ennf_transformation,[],[f7])).
% 2.58/0.70  fof(f7,axiom,(
% 2.58/0.70    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.58/0.70  fof(f271,plain,(
% 2.58/0.70    v1_xboole_0(k2_relat_1(sK2)) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f121,f231,f168,f163,f65])).
% 2.58/0.70  fof(f65,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f22])).
% 2.58/0.70  fof(f22,plain,(
% 2.58/0.70    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.58/0.70    inference(flattening,[],[f21])).
% 2.58/0.70  fof(f21,plain,(
% 2.58/0.70    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.58/0.70    inference(ennf_transformation,[],[f12])).
% 2.58/0.70  fof(f12,axiom,(
% 2.58/0.70    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.58/0.70  fof(f168,plain,(
% 2.58/0.70    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~spl10_1),
% 2.58/0.70    inference(forward_demodulation,[],[f153,f146])).
% 2.58/0.70  fof(f153,plain,(
% 2.58/0.70    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl10_1),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f121,f151,f60])).
% 2.58/0.70  fof(f60,plain,(
% 2.58/0.70    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f20])).
% 2.58/0.70  fof(f20,plain,(
% 2.58/0.70    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/0.70    inference(flattening,[],[f19])).
% 2.58/0.70  fof(f19,plain,(
% 2.58/0.70    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f14])).
% 2.58/0.70  fof(f14,axiom,(
% 2.58/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 2.58/0.70  fof(f231,plain,(
% 2.58/0.70    ~v1_partfun1(sK2,sK0) | (~spl10_1 | spl10_2 | ~spl10_3)),
% 2.58/0.70    inference(unit_resulting_resolution,[],[f121,f126,f129,f79])).
% 2.58/0.70  fof(f79,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f30])).
% 2.58/0.70  fof(f30,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(flattening,[],[f29])).
% 2.58/0.70  fof(f29,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(ennf_transformation,[],[f11])).
% 2.58/0.71  fof(f11,axiom,(
% 2.58/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 2.58/0.71  fof(f129,plain,(
% 2.58/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_3),
% 2.58/0.71    inference(avatar_component_clause,[],[f128])).
% 2.58/0.71  fof(f128,plain,(
% 2.58/0.71    spl10_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.58/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.58/0.71  fof(f163,plain,(
% 2.58/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 2.58/0.71    inference(forward_demodulation,[],[f158,f146])).
% 2.58/0.71  fof(f158,plain,(
% 2.58/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 2.58/0.71    inference(unit_resulting_resolution,[],[f100,f100,f151,f75])).
% 2.58/0.71  fof(f75,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.58/0.71    inference(cnf_transformation,[],[f26])).
% 2.58/0.71  fof(f26,plain,(
% 2.58/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.58/0.71    inference(flattening,[],[f25])).
% 2.58/0.71  fof(f25,plain,(
% 2.58/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.58/0.71    inference(ennf_transformation,[],[f10])).
% 2.58/0.71  fof(f10,axiom,(
% 2.58/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 2.58/0.71  fof(f100,plain,(
% 2.58/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.58/0.71    inference(equality_resolution,[],[f68])).
% 2.58/0.71  fof(f68,plain,(
% 2.58/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.58/0.71    inference(cnf_transformation,[],[f43])).
% 2.58/0.71  fof(f43,plain,(
% 2.58/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.71    inference(flattening,[],[f42])).
% 2.58/0.71  fof(f42,plain,(
% 2.58/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.71    inference(nnf_transformation,[],[f3])).
% 2.58/0.71  fof(f3,axiom,(
% 2.58/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.58/0.71  fof(f229,plain,(
% 2.58/0.71    spl10_3),
% 2.58/0.71    inference(avatar_split_clause,[],[f228,f128])).
% 2.58/0.71  fof(f228,plain,(
% 2.58/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.58/0.71    inference(forward_demodulation,[],[f219,f146])).
% 2.58/0.71  fof(f219,plain,(
% 2.58/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.58/0.71    inference(unit_resulting_resolution,[],[f151,f101,f147,f75])).
% 2.58/0.71  fof(f147,plain,(
% 2.58/0.71    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.58/0.71    inference(backward_demodulation,[],[f136,f134])).
% 2.58/0.71  fof(f136,plain,(
% 2.58/0.71    r1_tarski(k2_relat_1(sK8(sK0,sK1,sK2)),sK1)),
% 2.58/0.71    inference(unit_resulting_resolution,[],[f57,f112])).
% 2.58/0.71  fof(f112,plain,(
% 2.58/0.71    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.58/0.71    inference(equality_resolution,[],[f91])).
% 2.58/0.71  fof(f91,plain,(
% 2.58/0.71    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.58/0.71    inference(cnf_transformation,[],[f56])).
% 2.58/0.71  fof(f101,plain,(
% 2.58/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.58/0.71    inference(equality_resolution,[],[f67])).
% 2.58/0.71  fof(f67,plain,(
% 2.58/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.58/0.71    inference(cnf_transformation,[],[f43])).
% 2.58/0.71  fof(f152,plain,(
% 2.58/0.71    spl10_1),
% 2.58/0.71    inference(avatar_split_clause,[],[f148,f120])).
% 2.58/0.71  fof(f148,plain,(
% 2.58/0.71    v1_funct_1(sK2)),
% 2.58/0.71    inference(forward_demodulation,[],[f133,f134])).
% 2.58/0.71  fof(f133,plain,(
% 2.58/0.71    v1_funct_1(sK8(sK0,sK1,sK2))),
% 2.58/0.71    inference(unit_resulting_resolution,[],[f57,f115])).
% 2.58/0.71  fof(f115,plain,(
% 2.58/0.71    ( ! [X6,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 2.58/0.71    inference(equality_resolution,[],[f88])).
% 2.58/0.71  fof(f88,plain,(
% 2.58/0.71    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 2.58/0.71    inference(cnf_transformation,[],[f56])).
% 2.58/0.71  fof(f131,plain,(
% 2.58/0.71    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 2.58/0.71    inference(avatar_split_clause,[],[f58,f128,f124,f120])).
% 2.58/0.71  fof(f58,plain,(
% 2.58/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.58/0.71    inference(cnf_transformation,[],[f37])).
% 2.58/0.71  % SZS output end Proof for theBenchmark
% 2.58/0.71  % (14058)------------------------------
% 2.58/0.71  % (14058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.71  % (14058)Termination reason: Refutation
% 2.58/0.71  
% 2.58/0.71  % (14058)Memory used [KB]: 11385
% 2.58/0.71  % (14058)Time elapsed: 0.247 s
% 2.58/0.71  % (14058)------------------------------
% 2.58/0.71  % (14058)------------------------------
% 2.58/0.71  % (14021)Success in time 0.351 s
%------------------------------------------------------------------------------
