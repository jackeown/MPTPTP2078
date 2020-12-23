%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1079+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 21.08s
% Output     : Refutation 21.14s
% Verified   : 
% Statistics : Number of formulae       :  104 (1472 expanded)
%              Number of leaves         :   18 ( 747 expanded)
%              Depth                    :   23
%              Number of atoms          :  593 (12571 expanded)
%              Number of equality atoms :   94 (1903 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21025,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20986,f10249])).

fof(f10249,plain,(
    r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f10248,f3449])).

fof(f3449,plain,(
    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f2258,f2261,f2264,f2262,f2263,f2367])).

fof(f2367,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1743])).

fof(f1743,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1742])).

fof(f1742,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1548])).

fof(f1548,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f2263,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2009,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    & v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1705,f2008,f2007,f2006,f2005,f2004])).

fof(f2004,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(sK0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,X1,k4_funct_2(sK0,X1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,X1,X2,X3),X4))
                      & m1_subset_1(X4,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,sK0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2005,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k3_funct_2(sK0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,X1,k4_funct_2(sK0,X1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,X1,X2,X3),X4))
                    & m1_subset_1(X4,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(X1,X2))))
                & v1_funct_2(X3,sK0,k2_zfmisc_1(X1,X2))
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k3_funct_2(sK0,k2_zfmisc_1(sK1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,sK1,X2,X3),X4))
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,X2))))
              & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,X2))
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2006,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k3_funct_2(sK0,k2_zfmisc_1(sK1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,sK1,X2,X3),X4))
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,X2))))
            & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,X2))
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,X3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,X3),X4))
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
          & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,sK2))
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2007,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,X3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,X3),X4))
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,sK2))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X4))
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
      & v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2008,plain,
    ( ? [X4] :
        ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X4))
        & m1_subset_1(X4,sK0) )
   => ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1705,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1704])).

fof(f1704,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1635])).

fof(f1635,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                      & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1634])).

fof(f1634,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_funct_2)).

fof(f2262,plain,(
    v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2264,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2261,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2258,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f2009])).

fof(f10248,plain,(
    r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f10005,f3462])).

fof(f3462,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f2263,f2920])).

fof(f2920,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1979])).

fof(f1979,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f10005,plain,(
    r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(unit_resulting_resolution,[],[f2258,f2261,f2264,f2262,f2263,f3401,f2371])).

fof(f2371,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1749])).

fof(f1749,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1748])).

fof(f1748,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1626])).

fof(f1626,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

fof(f3401,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2259,f2260,f2412])).

fof(f2412,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1779])).

fof(f1779,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1778])).

fof(f1778,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f475])).

fof(f475,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f2260,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2259,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f2009])).

fof(f20986,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f3448,f20056,f2643])).

fof(f2643,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1921])).

fof(f1921,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1920])).

fof(f1920,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1338])).

fof(f1338,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f20056,plain,(
    k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4))) ),
    inference(backward_demodulation,[],[f20027,f20037])).

fof(f20037,plain,(
    k2_mcart_1(k1_funct_1(sK3,sK4)) = k1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3),sK4) ),
    inference(backward_demodulation,[],[f19946,f20036])).

fof(f20036,plain,(
    k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k1_funct_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f19944,f3449])).

fof(f19944,plain,(
    k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2264,f2262,f3442,f2263,f3443,f3444,f2988])).

fof(f2988,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f2358])).

fof(f2358,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | k5_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X4,X0,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2086,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ( k3_funct_2(X0,X2,X4,sK48(X0,X1,X2,X3,X4)) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK48(X0,X1,X2,X3,X4)))
                            & m1_subset_1(sK48(X0,X1,X2,X3,X4),X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK48])],[f2084,f2085])).

fof(f2085,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X2,X4,sK48(X0,X1,X2,X3,X4)) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK48(X0,X1,X2,X3,X4)))
        & m1_subset_1(sK48(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2084,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f2083])).

fof(f2083,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              | ~ m1_subset_1(X5,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f1737])).

fof(f1737,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1736])).

fof(f1736,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1489])).

fof(f1489,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                        & v1_funct_2(X4,X0,X2)
                        & v1_funct_1(X4) )
                     => ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_funct_2)).

fof(f3444,plain,(
    m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2262,f2263,f2357])).

fof(f2357,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1735])).

fof(f1735,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1734])).

fof(f1734,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1503])).

fof(f1503,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_funct_2)).

fof(f3443,plain,(
    v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2262,f2263,f2356])).

fof(f2356,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1735])).

fof(f3442,plain,(
    v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2262,f2263,f2355])).

fof(f2355,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1735])).

fof(f19946,plain,(
    k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3),sK4) ),
    inference(unit_resulting_resolution,[],[f2258,f2264,f3442,f3443,f3444,f2367])).

fof(f20027,plain,(
    k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(backward_demodulation,[],[f3580,f19946])).

fof(f3580,plain,(
    k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(forward_demodulation,[],[f3579,f3449])).

fof(f3579,plain,(
    k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(subsumption_resolution,[],[f3578,f2258])).

fof(f3578,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3577,f2259])).

fof(f3577,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3576,f2260])).

fof(f3576,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3575,f2261])).

fof(f3575,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3574,f2262])).

fof(f3574,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3573,f2263])).

fof(f3573,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3572,f3445])).

fof(f3445,plain,(
    v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2262,f2263,f2361])).

fof(f2361,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f1739,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1738])).

fof(f1738,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1501])).

fof(f1501,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_funct_2)).

fof(f3572,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3571,f3446])).

fof(f3446,plain,(
    v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2262,f2263,f2362])).

fof(f2362,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f3571,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3570,f3447])).

fof(f3447,plain,(
    m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2258,f2259,f2260,f2261,f2262,f2263,f2363])).

fof(f2363,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f3570,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3566,f2264])).

fof(f3566,plain,
    ( k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ m1_subset_1(sK4,sK0)
    | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f3512,f2989])).

fof(f2989,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f2364])).

fof(f2364,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | k4_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2090])).

fof(f2090,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ( k3_funct_2(X0,X1,X4,sK49(X0,X1,X2,X3,X4)) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK49(X0,X1,X2,X3,X4)))
                            & m1_subset_1(sK49(X0,X1,X2,X3,X4),X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49])],[f2088,f2089])).

fof(f2089,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X4,sK49(X0,X1,X2,X3,X4)) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK49(X0,X1,X2,X3,X4)))
        & m1_subset_1(sK49(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2088,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f2087])).

fof(f2087,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              | ~ m1_subset_1(X5,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f1741])).

fof(f1741,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1740])).

fof(f1740,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1487])).

fof(f1487,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                        & v1_funct_2(X4,X0,X1)
                        & v1_funct_1(X4) )
                     => ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_funct_2)).

fof(f3512,plain,(
    k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) != k1_funct_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f2265,f3449])).

fof(f2265,plain,(
    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f2009])).

fof(f3448,plain,(
    v1_relat_1(k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f2263,f2543])).

fof(f2543,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_relat_1(k2_relat_1(X3)) ) ),
    inference(cnf_transformation,[],[f1850])).

fof(f1850,plain,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(k2_relat_1(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(ennf_transformation,[],[f1537])).

fof(f1537,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
     => v1_relat_1(k2_relat_1(X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relset_1)).
%------------------------------------------------------------------------------
