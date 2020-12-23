%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t34_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:44 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 743 expanded)
%              Number of leaves         :    9 ( 138 expanded)
%              Depth                    :   37
%              Number of atoms          :  660 (8129 expanded)
%              Number of equality atoms :  231 (3401 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f742,f749,f1241])).

fof(f1241,plain,
    ( ~ spl7_64
    | ~ spl7_66 ),
    inference(avatar_contradiction_clause,[],[f1240])).

fof(f1240,plain,
    ( $false
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1239,f732])).

fof(f732,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f731])).

fof(f731,plain,
    ( spl7_64
  <=> r2_hidden(sK4(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f1239,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f1238,f141])).

fof(f141,plain,(
    k2_relat_1(sK2) = sK1 ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t34_funct_2.p',t34_funct_2)).

fof(f138,plain,
    ( k2_relat_1(sK2) = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f59,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t34_funct_2.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f1238,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1237,f741])).

fof(f741,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f740])).

fof(f740,plain,
    ( spl7_66
  <=> r2_hidden(sK5(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1237,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f1236,f269])).

fof(f269,plain,(
    k1_relat_1(sK2) = sK0 ),
    inference(subsumption_resolution,[],[f266,f66])).

fof(f266,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f180,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t34_funct_2.p',redefinition_k1_relset_1)).

fof(f180,plain,(
    k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(subsumption_resolution,[],[f179,f65])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f179,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f174,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f66,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t34_funct_2.p',d1_funct_2)).

fof(f1236,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1235,f202])).

fof(f202,plain,(
    k1_relat_1(sK3) = sK1 ),
    inference(subsumption_resolution,[],[f199,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f199,plain,
    ( k1_relat_1(sK3) = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f127,f91])).

fof(f127,plain,(
    k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(subsumption_resolution,[],[f126,f57])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f126,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f121,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f121,plain,
    ( k1_xboole_0 = sK0
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f58,f99])).

fof(f1235,plain,
    ( k1_relat_1(sK3) != sK1
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f1234,f141])).

fof(f1234,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1233,f63])).

fof(f63,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f1233,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1232,f175])).

fof(f175,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t34_funct_2.p',cc1_relset_1)).

fof(f1232,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1231,f1190])).

fof(f1190,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1189,f63])).

fof(f1189,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1188,f175])).

fof(f1188,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1187,f60])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1187,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1186,f64])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1186,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1185,f732])).

fof(f1185,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f1168,f141])).

fof(f1168,plain,
    ( k2_relat_1(sK2) != sK1
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(trivial_inequality_removal,[],[f1167])).

fof(f1167,plain,
    ( sK4(sK2,sK3) != sK4(sK2,sK3)
    | k2_relat_1(sK2) != sK1
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = sK4(sK2,sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(equality_factoring,[],[f402])).

fof(f402,plain,(
    ! [X2] :
      ( k1_funct_1(sK2,sK5(X2,sK3)) = sK4(X2,sK3)
      | k2_relat_1(X2) != sK1
      | ~ r2_hidden(sK4(X2,sK3),sK1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK5(X2,sK3)) = sK4(X2,sK3)
      | k2_funct_1(X2) = sK3 ) ),
    inference(forward_demodulation,[],[f401,f202])).

fof(f401,plain,(
    ! [X2] :
      ( k1_funct_1(sK2,sK5(X2,sK3)) = sK4(X2,sK3)
      | ~ r2_hidden(sK4(X2,sK3),sK1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_relat_1(sK3) != k2_relat_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK5(X2,sK3)) = sK4(X2,sK3)
      | k2_funct_1(X2) = sK3 ) ),
    inference(subsumption_resolution,[],[f400,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f400,plain,(
    ! [X2] :
      ( k1_funct_1(sK2,sK5(X2,sK3)) = sK4(X2,sK3)
      | ~ r2_hidden(sK4(X2,sK3),sK1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK5(X2,sK3)) = sK4(X2,sK3)
      | k2_funct_1(X2) = sK3 ) ),
    inference(subsumption_resolution,[],[f390,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f58,f89])).

fof(f390,plain,(
    ! [X2] :
      ( k1_funct_1(sK2,sK5(X2,sK3)) = sK4(X2,sK3)
      | ~ r2_hidden(sK4(X2,sK3),sK1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK5(X2,sK3)) = sK4(X2,sK3)
      | k2_funct_1(X2) = sK3 ) ),
    inference(superposition,[],[f102,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK4(X0,X1)) = sK5(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t34_funct_2.p',t54_funct_1)).

fof(f102,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4
      | ~ r2_hidden(X4,sK1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) != X5
      | k1_funct_1(sK2,X5) = X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1231,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != sK4(sK2,sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1230,f56])).

fof(f1230,plain,
    ( ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != sK4(sK2,sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1229,f122])).

fof(f1229,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != sK4(sK2,sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1228,f60])).

fof(f1228,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != sK4(sK2,sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1227,f64])).

fof(f1227,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != sK4(sK2,sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(trivial_inequality_removal,[],[f1224])).

fof(f1224,plain,
    ( sK5(sK2,sK3) != sK5(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != sK4(sK2,sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(superposition,[],[f73,f1201])).

fof(f1201,plain,
    ( k1_funct_1(sK3,sK4(sK2,sK3)) = sK5(sK2,sK3)
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1191,f741])).

fof(f1191,plain,
    ( k1_funct_1(sK3,sK4(sK2,sK3)) = sK5(sK2,sK3)
    | ~ r2_hidden(sK5(sK2,sK3),sK0)
    | ~ spl7_64 ),
    inference(superposition,[],[f104,f1190])).

fof(f104,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,k1_funct_1(sK2,X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK2,X5) != X4
      | k1_funct_1(sK3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k1_funct_1(X0,sK5(X0,X1)) != sK4(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f749,plain,(
    spl7_65 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f747,f63])).

fof(f747,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f746,f56])).

fof(f746,plain,
    ( ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f745,f122])).

fof(f745,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f743,f202])).

fof(f743,plain,
    ( k1_relat_1(sK3) != sK1
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ spl7_65 ),
    inference(resolution,[],[f735,f311])).

fof(f311,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k2_funct_1(sK2) = X0 ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | k1_relat_1(X0) != sK1
      | r2_hidden(sK4(sK2,X0),sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k2_funct_1(sK2) = X0 ) ),
    inference(forward_demodulation,[],[f309,f141])).

fof(f309,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK4(sK2,X0),sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f308,f284])).

fof(f284,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK0)
      | k1_relat_1(X1) != sK1
      | r2_hidden(sK4(sK2,X1),sK1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_funct_1(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f283,f141])).

fof(f283,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f282,f141])).

fof(f282,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f281,f175])).

fof(f281,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f280,f60])).

fof(f280,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK0)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f273,f64])).

fof(f273,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,X1),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X1),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X1 ) ),
    inference(superposition,[],[f78,f269])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f308,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK4(sK2,X0),sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X0 ) ),
    inference(forward_demodulation,[],[f307,f141])).

fof(f307,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | k2_funct_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f306,f175])).

fof(f306,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f305,f60])).

fof(f305,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f291,f64])).

fof(f291,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X0 ) ),
    inference(superposition,[],[f105,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    ! [X5] :
      ( r2_hidden(k1_funct_1(sK2,X5),sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK2,X5) != X4
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f735,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl7_65
  <=> ~ r2_hidden(sK4(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f742,plain,
    ( ~ spl7_65
    | spl7_66 ),
    inference(avatar_split_clause,[],[f729,f740,f734])).

fof(f729,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f728,f63])).

fof(f728,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f727,f141])).

fof(f727,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f726,f175])).

fof(f726,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f725,f60])).

fof(f725,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f721,f64])).

fof(f721,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3 ),
    inference(duplicate_literal_removal,[],[f720])).

fof(f720,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3 ),
    inference(superposition,[],[f254,f269])).

fof(f254,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK3),k1_relat_1(X1))
      | r2_hidden(sK5(X1,sK3),sK0)
      | ~ r2_hidden(sK4(X1,sK3),sK1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) != sK1
      | k2_funct_1(X1) = sK3 ) ),
    inference(forward_demodulation,[],[f253,f202])).

fof(f253,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK3),sK0)
      | ~ r2_hidden(sK4(X1,sK3),sK1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | k1_relat_1(sK3) != k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK5(X1,sK3),k1_relat_1(X1))
      | k2_funct_1(X1) = sK3 ) ),
    inference(subsumption_resolution,[],[f252,f56])).

fof(f252,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK3),sK0)
      | ~ r2_hidden(sK4(X1,sK3),sK1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK5(X1,sK3),k1_relat_1(X1))
      | k2_funct_1(X1) = sK3 ) ),
    inference(subsumption_resolution,[],[f239,f122])).

fof(f239,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK3),sK0)
      | ~ r2_hidden(sK4(X1,sK3),sK1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK5(X1,sK3),k1_relat_1(X1))
      | k2_funct_1(X1) = sK3 ) ),
    inference(superposition,[],[f103,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK4(X0,X1)) = sK5(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK3,X4),sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
