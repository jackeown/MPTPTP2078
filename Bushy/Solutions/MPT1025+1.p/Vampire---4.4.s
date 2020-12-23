%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t116_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 141 expanded)
%              Number of leaves         :    6 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 914 expanded)
%              Number of equality atoms :   22 ( 142 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f111])).

fof(f111,plain,(
    m1_subset_1(sK5(sK0,sK2,sK3,sK4),sK0) ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t116_funct_2.p',t1_subset)).

fof(f93,plain,(
    r2_hidden(sK5(sK0,sK2,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK4
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t116_funct_2.p',t116_funct_2)).

fof(f92,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3,sK4),sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f47,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3,sK4),sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X2,X3,X4),X0)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4
            & r2_hidden(sK5(X0,X2,X3,X4),X2)
            & r2_hidden(sK5(X0,X2,X3,X4),X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f42])).

fof(f42,plain,(
    ! [X4,X3,X2,X0] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4
        & r2_hidden(sK5(X0,X2,X3,X4),X2)
        & r2_hidden(sK5(X0,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t116_funct_2.p',t115_funct_2)).

fof(f49,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f140,plain,(
    ~ m1_subset_1(sK5(sK0,sK2,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f133,f99])).

fof(f99,plain,(
    k1_funct_1(sK3,sK5(sK0,sK2,sK3,sK4)) = sK4 ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK2,sK3,sK4)) = sK4
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f97,f47])).

fof(f97,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK2,sK3,sK4)) = sK4
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f84,f48])).

fof(f84,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK2,sK3,sK4)) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f133,plain,
    ( k1_funct_1(sK3,sK5(sK0,sK2,sK3,sK4)) != sK4
    | ~ m1_subset_1(sK5(sK0,sK2,sK3,sK4),sK0) ),
    inference(resolution,[],[f96,f50])).

fof(f50,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | k1_funct_1(sK3,X5) != sK4
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    r2_hidden(sK5(sK0,sK2,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f95,f46])).

fof(f95,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3,sK4),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f94,f47])).

fof(f94,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3,sK4),sK2)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f83,f48])).

fof(f83,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
