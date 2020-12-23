%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 (1146 expanded)
%              Number of leaves         :   14 ( 415 expanded)
%              Depth                    :   29
%              Number of atoms          :  482 (8936 expanded)
%              Number of equality atoms :   92 (1258 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(subsumption_resolution,[],[f490,f216])).

fof(f216,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f215,f69])).

fof(f69,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f38,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
    & v2_funct_1(sK4)
    & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
      & v2_funct_1(sK4)
      & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f215,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f43,f76])).

fof(f76,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f40,f47])).

fof(f40,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f490,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f489,f69])).

fof(f489,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f488,f76])).

fof(f488,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f487,f252])).

fof(f252,plain,(
    k2_struct_0(sK3) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f251,f69])).

fof(f251,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f44,f76])).

fof(f44,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f487,plain,
    ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f486,f69])).

fof(f486,plain,
    ( k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f485,f76])).

fof(f485,plain,
    ( k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f484,f413])).

fof(f413,plain,(
    k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f374,f351])).

fof(f351,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(resolution,[],[f295,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f295,plain,(
    sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f294,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f294,plain,
    ( sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f293,f202])).

fof(f202,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f129,f76])).

fof(f129,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f42,f69])).

fof(f42,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f293,plain,
    ( sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f292,f216])).

fof(f292,plain,
    ( sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f286,f45])).

fof(f45,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f286,plain,
    ( sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f59,f252])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f22,f29])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f374,plain,
    ( k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f373,f231])).

fof(f231,plain,(
    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) ),
    inference(subsumption_resolution,[],[f230,f41])).

fof(f230,plain,
    ( r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f222,f202])).

fof(f222,plain,
    ( r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f216,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f373,plain,
    ( ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f372,f238])).

fof(f238,plain,(
    sK4 = k2_funct_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f225,f96])).

fof(f96,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k2_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f90,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f45,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f225,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f216,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f372,plain,
    ( ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f371,f247])).

fof(f247,plain,(
    v1_funct_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f239,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f239,plain,(
    sP0(sK4) ),
    inference(resolution,[],[f225,f97])).

fof(f97,plain,
    ( ~ v1_relat_1(sK4)
    | sP0(sK4) ),
    inference(subsumption_resolution,[],[f91,f41])).

fof(f91,plain,
    ( sP0(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f27])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f371,plain,
    ( ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f370,f350])).

fof(f350,plain,(
    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f295,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f370,plain,
    ( ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f369,f248])).

fof(f248,plain,(
    v2_funct_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f239,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f369,plain,
    ( ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(superposition,[],[f368,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f368,plain,(
    ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    inference(backward_demodulation,[],[f338,f291])).

fof(f291,plain,(
    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f290,f41])).

fof(f290,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f289,f202])).

fof(f289,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f288,f216])).

fof(f288,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f287,f45])).

fof(f287,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f60,f252])).

fof(f338,plain,(
    ~ r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) ),
    inference(forward_demodulation,[],[f337,f69])).

fof(f337,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) ),
    inference(forward_demodulation,[],[f46,f76])).

fof(f46,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f484,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f483,f291])).

fof(f483,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f482,f69])).

fof(f482,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f119,f76])).

fof(f119,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f118,f38])).

fof(f118,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f116,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f115,f41])).

fof(f115,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f102,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:09:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.44  % (7937)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.45  % (7933)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.46  % (7941)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.46  % (7937)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f491,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f490,f216])).
% 0.20/0.46  fof(f216,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f215,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.46    inference(resolution,[],[f38,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    l1_struct_0(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f33,f32,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f43,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.20/0.46    inference(resolution,[],[f40,f47])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    l1_struct_0(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f490,plain,(
% 0.20/0.46    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f489,f69])).
% 0.20/0.46  fof(f489,plain,(
% 0.20/0.46    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f488,f76])).
% 0.20/0.46  fof(f488,plain,(
% 0.20/0.46    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(subsumption_resolution,[],[f487,f252])).
% 0.20/0.46  fof(f252,plain,(
% 0.20/0.46    k2_struct_0(sK3) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.46    inference(forward_demodulation,[],[f251,f69])).
% 0.20/0.46  fof(f251,plain,(
% 0.20/0.46    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.46    inference(forward_demodulation,[],[f44,f76])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f487,plain,(
% 0.20/0.46    k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f486,f69])).
% 0.20/0.46  fof(f486,plain,(
% 0.20/0.46    k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f485,f76])).
% 0.20/0.46  fof(f485,plain,(
% 0.20/0.46    k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(subsumption_resolution,[],[f484,f413])).
% 0.20/0.46  fof(f413,plain,(
% 0.20/0.46    k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.20/0.46    inference(subsumption_resolution,[],[f374,f351])).
% 0.20/0.46  fof(f351,plain,(
% 0.20/0.46    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.20/0.46    inference(resolution,[],[f295,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.46    inference(nnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.46  fof(f295,plain,(
% 0.20/0.46    sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f294,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    v1_funct_1(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f294,plain,(
% 0.20/0.46    sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f293,f202])).
% 0.20/0.46  fof(f202,plain,(
% 0.20/0.46    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))),
% 0.20/0.46    inference(forward_demodulation,[],[f129,f76])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.46    inference(backward_demodulation,[],[f42,f69])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f293,plain,(
% 0.20/0.46    sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f292,f216])).
% 0.20/0.46  fof(f292,plain,(
% 0.20/0.46    sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f286,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    v2_funct_1(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f286,plain,(
% 0.20/0.46    sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f285])).
% 0.20/0.46  fof(f285,plain,(
% 0.20/0.46    k2_struct_0(sK3) != k2_struct_0(sK3) | sP1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(superposition,[],[f59,f252])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (sP1(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.46    inference(definition_folding,[],[f22,f29])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.46    inference(flattening,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.46  fof(f374,plain,(
% 0.20/0.46    k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.20/0.46    inference(subsumption_resolution,[],[f373,f231])).
% 0.20/0.46  fof(f231,plain,(
% 0.20/0.46    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f230,f41])).
% 0.20/0.46  fof(f230,plain,(
% 0.20/0.46    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f222,f202])).
% 0.20/0.46  fof(f222,plain,(
% 0.20/0.46    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(resolution,[],[f216,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.46    inference(equality_resolution,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.46    inference(nnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.46    inference(flattening,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.20/0.46  fof(f373,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4,sK4) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.20/0.46    inference(forward_demodulation,[],[f372,f238])).
% 0.20/0.46  fof(f238,plain,(
% 0.20/0.46    sK4 = k2_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(resolution,[],[f225,f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ~v1_relat_1(sK4) | sK4 = k2_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(subsumption_resolution,[],[f90,f41])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.46    inference(resolution,[],[f45,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.46  fof(f225,plain,(
% 0.20/0.46    v1_relat_1(sK4)),
% 0.20/0.46    inference(resolution,[],[f216,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.46  fof(f372,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.20/0.46    inference(subsumption_resolution,[],[f371,f247])).
% 0.20/0.46  fof(f247,plain,(
% 0.20/0.46    v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(resolution,[],[f239,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.46  fof(f239,plain,(
% 0.20/0.46    sP0(sK4)),
% 0.20/0.46    inference(resolution,[],[f225,f97])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    ~v1_relat_1(sK4) | sP0(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f91,f41])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    sP0(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.46    inference(resolution,[],[f45,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(definition_folding,[],[f17,f27])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.46  fof(f371,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(subsumption_resolution,[],[f370,f350])).
% 0.20/0.46  fof(f350,plain,(
% 0.20/0.46    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.20/0.46    inference(resolution,[],[f295,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f36])).
% 0.20/0.46  fof(f370,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(subsumption_resolution,[],[f369,f248])).
% 0.20/0.46  fof(f248,plain,(
% 0.20/0.46    v2_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(resolution,[],[f239,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f35])).
% 0.20/0.46  fof(f369,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) | ~v2_funct_1(k2_funct_1(sK4)) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.46    inference(superposition,[],[f368,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.46    inference(flattening,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.46  fof(f368,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 0.20/0.46    inference(backward_demodulation,[],[f338,f291])).
% 0.20/0.46  fof(f291,plain,(
% 0.20/0.46    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f290,f41])).
% 0.20/0.46  fof(f290,plain,(
% 0.20/0.46    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f289,f202])).
% 0.20/0.46  fof(f289,plain,(
% 0.20/0.46    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f288,f216])).
% 0.20/0.46  fof(f288,plain,(
% 0.20/0.46    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f287,f45])).
% 0.20/0.46  fof(f287,plain,(
% 0.20/0.46    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f284])).
% 0.20/0.46  fof(f284,plain,(
% 0.20/0.46    k2_struct_0(sK3) != k2_struct_0(sK3) | k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.46    inference(superposition,[],[f60,f252])).
% 0.20/0.46  fof(f338,plain,(
% 0.20/0.46    ~r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)),
% 0.20/0.46    inference(forward_demodulation,[],[f337,f69])).
% 0.20/0.46  fof(f337,plain,(
% 0.20/0.46    ~r2_funct_2(u1_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)),
% 0.20/0.46    inference(forward_demodulation,[],[f46,f76])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f484,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f483,f291])).
% 0.20/0.46  fof(f483,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f482,f69])).
% 0.20/0.46  fof(f482,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(forward_demodulation,[],[f119,f76])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.46    inference(subsumption_resolution,[],[f118,f38])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~l1_struct_0(sK2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f117,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ~v2_struct_0(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f116,f40])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f115,f41])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f102,f45])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.46    inference(resolution,[],[f42,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (7937)------------------------------
% 0.20/0.46  % (7937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (7937)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (7937)Memory used [KB]: 1918
% 0.20/0.46  % (7937)Time elapsed: 0.080 s
% 0.20/0.46  % (7937)------------------------------
% 0.20/0.46  % (7937)------------------------------
% 0.20/0.46  % (7928)Success in time 0.121 s
%------------------------------------------------------------------------------
