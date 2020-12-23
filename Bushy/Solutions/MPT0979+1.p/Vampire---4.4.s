%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t25_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 993 expanded)
%              Number of leaves         :   14 ( 264 expanded)
%              Depth                    :   21
%              Number of atoms          :  528 (9239 expanded)
%              Number of equality atoms :  171 (3662 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f119,f226,f269,f331,f399])).

fof(f399,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f374,f138])).

fof(f138,plain,
    ( sK5(sK2) != sK6(sK2)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f124,f57,f99,f70])).

fof(f70,plain,(
    ! [X0] :
      ( sK5(X0) != sK6(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK5(X0) != sK6(X0)
            & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
            & r2_hidden(sK6(X0),k1_relat_1(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK5(X0) != sK6(X0)
        & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t25_funct_2.p',d8_funct_1)).

fof(f99,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_1
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ( sK3 != sK4
        & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
        & r2_hidden(sK4,sK0)
        & r2_hidden(sK3,sK0) )
      | ~ v2_funct_1(sK2) )
    & ( ! [X5,X6] :
          ( X5 = X6
          | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
          | ~ r2_hidden(X6,sK0)
          | ~ r2_hidden(X5,sK0) )
      | v2_funct_1(sK2) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) )
        & ( ! [X5,X6] :
              ( X5 = X6
              | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
              | ~ r2_hidden(X6,X0)
              | ~ r2_hidden(X5,X0) )
          | v2_funct_1(X2) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ? [X4,X3] :
            ( X3 != X4
            & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
            & r2_hidden(X4,sK0)
            & r2_hidden(X3,sK0) )
        | ~ v2_funct_1(sK2) )
      & ( ! [X6,X5] :
            ( X5 = X6
            | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
            | ~ r2_hidden(X6,sK0)
            | ~ r2_hidden(X5,sK0) )
        | v2_funct_1(sK2) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ? [X3,X4] :
          ( X3 != X4
          & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
          & r2_hidden(X4,X0)
          & r2_hidden(X3,X0) )
     => ( sK3 != sK4
        & k1_funct_1(X2,sK3) = k1_funct_1(X2,sK4)
        & r2_hidden(sK4,X0)
        & r2_hidden(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X5,X6] :
            ( X5 = X6
            | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
            | ~ r2_hidden(X6,X0)
            | ~ r2_hidden(X5,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v2_funct_1(X2)
          <=> ! [X3,X4] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  & r2_hidden(X4,X0)
                  & r2_hidden(X3,X0) )
               => X3 = X4 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t25_funct_2.p',t25_funct_2)).

fof(f124,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f59,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t25_funct_2.p',cc1_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f374,plain,
    ( sK5(sK2) = sK6(sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f345,f349,f147,f351])).

fof(f351,plain,
    ( ! [X6,X5] :
        ( k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
        | ~ r2_hidden(X6,k1_xboole_0)
        | ~ r2_hidden(X5,k1_xboole_0)
        | X5 = X6 )
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f350,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f350,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
        | X5 = X6
        | ~ r2_hidden(X5,sK0) )
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f120,f118])).

fof(f120,plain,
    ( ! [X6,X5] :
        ( k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
        | X5 = X6
        | ~ r2_hidden(X6,sK0)
        | ~ r2_hidden(X5,sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f61,f99])).

fof(f61,plain,(
    ! [X6,X5] :
      ( X5 = X6
      | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
      | ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X5,sK0)
      | v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f147,plain,
    ( k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f99,f57,f124,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f349,plain,
    ( r2_hidden(sK5(sK2),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f131,f305])).

fof(f305,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f304,f291])).

fof(f291,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f288,f290,f93])).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t25_funct_2.p',d1_funct_2)).

fof(f290,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f271,f118])).

fof(f271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f109,f59])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f288,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f270,f118])).

fof(f270,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f109,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f304,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f303,f118])).

fof(f303,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f143,f109])).

fof(f143,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f59,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t25_funct_2.p',redefinition_k1_relset_1)).

fof(f131,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f99,f57,f124,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f345,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f136,f305])).

fof(f136,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f99,f57,f124,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f331,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f329,f243])).

fof(f243,plain,
    ( sK3 != sK4
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f65,f96])).

fof(f96,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_0
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f65,plain,
    ( sK3 != sK4
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f329,plain,
    ( sK3 = sK4
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f326,f272])).

fof(f272,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f118,f105])).

fof(f105,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f326,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | sK3 = sK4
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(equality_resolution,[],[f322])).

fof(f322,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | sK4 = X0 )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f321,f305])).

fof(f321,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f320,f276])).

fof(f276,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f118,f236])).

fof(f236,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f63,f96])).

fof(f63,plain,
    ( r2_hidden(sK4,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k1_xboole_0)
        | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f249,f305])).

fof(f249,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f248,f124])).

fof(f248,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f247,f57])).

fof(f247,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f245,f96])).

fof(f245,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_0 ),
    inference(superposition,[],[f66,f244])).

fof(f244,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f64,f96])).

fof(f64,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f66,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f269,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f267,f243])).

fof(f267,plain,
    ( sK3 = sK4
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f264,f105])).

fof(f264,plain,
    ( ~ r2_hidden(sK3,sK0)
    | sK3 = sK4
    | ~ spl8_0
    | ~ spl8_5 ),
    inference(equality_resolution,[],[f252])).

fof(f252,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,sK0)
        | sK4 = X0 )
    | ~ spl8_0
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f251,f162])).

fof(f162,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f143,f150])).

fof(f150,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f112,f58,f59,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f251,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_0
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f250,f236])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,sK0)
        | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_0
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f249,f162])).

fof(f226,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f201,f138])).

fof(f201,plain,
    ( sK5(sK2) = sK6(sK2)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f163,f167,f147,f120])).

fof(f167,plain,
    ( r2_hidden(sK6(sK2),sK0)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f162,f136])).

fof(f163,plain,
    ( r2_hidden(sK5(sK2),sK0)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f162,f131])).

fof(f119,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f60,f117,f111])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f104,f98])).

fof(f62,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
