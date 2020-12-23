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
% DateTime   : Thu Dec  3 13:09:35 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  220 (3035 expanded)
%              Number of leaves         :   21 (1066 expanded)
%              Depth                    :   27
%              Number of atoms          : 1188 (39620 expanded)
%              Number of equality atoms :   90 (3062 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1982,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1981,f1942])).

fof(f1942,plain,(
    ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f1941,f1880])).

fof(f1880,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f1879,f1468])).

fof(f1468,plain,
    ( ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f571,f759])).

fof(f759,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(resolution,[],[f564,f269])).

fof(f269,plain,(
    r1_tarski(k1_relat_1(sK6),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f268,f234])).

fof(f234,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f70,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | ~ v5_pre_topc(sK6,sK4,sK5) )
    & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | v5_pre_topc(sK6,sK4,sK5) )
    & sK6 = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f46,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK4,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK4,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK4,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK4,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                | ~ v5_pre_topc(X2,sK4,sK5) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                | v5_pre_topc(X2,sK4,sK5) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
          & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
              | ~ v5_pre_topc(X2,sK4,sK5) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
              | v5_pre_topc(X2,sK4,sK5) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
        & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
            | ~ v5_pre_topc(sK6,sK4,sK5) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
            | v5_pre_topc(sK6,sK4,sK5) )
          & sK6 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
      & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
          | ~ v5_pre_topc(sK6,sK4,sK5) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
          | v5_pre_topc(sK6,sK4,sK5) )
        & sK6 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
        | ~ v5_pre_topc(sK6,sK4,sK5) )
      & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
        | v5_pre_topc(sK6,sK4,sK5) )
      & sK6 = sK7
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
      & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f268,plain,
    ( r1_tarski(k1_relat_1(sK6),u1_struct_0(sK4))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f236,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f236,plain,(
    v4_relat_1(sK6,u1_struct_0(sK4)) ),
    inference(resolution,[],[f70,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f564,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK6),X0)
      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ) ),
    inference(resolution,[],[f371,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f371,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(cnf_transformation,[],[f51])).

fof(f571,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f570,f64])).

fof(f64,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f570,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f569,f65])).

fof(f65,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f569,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f568,f166])).

fof(f166,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f157,f66])).

fof(f66,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f157,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f67,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f67,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f568,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f567,f297])).

fof(f297,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(resolution,[],[f156,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f156,plain,(
    m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(resolution,[],[f67,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f567,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f566,f68])).

fof(f68,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f566,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f550,f277])).

fof(f277,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(forward_demodulation,[],[f72,f74])).

fof(f72,plain,(
    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f550,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f371,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f1879,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f660,f759])).

fof(f660,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f659,f64])).

fof(f659,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f658,f65])).

fof(f658,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f657,f66])).

fof(f657,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f656,f67])).

fof(f656,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f655,f69])).

fof(f69,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f655,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f654,f70])).

fof(f654,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f646,f68])).

fof(f646,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f513,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f513,plain,
    ( v5_pre_topc(sK6,sK4,sK5)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f75,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f1941,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f1940,f1528])).

fof(f1528,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f577,f759])).

fof(f577,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f576,f64])).

fof(f576,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f575,f65])).

fof(f575,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f574,f166])).

fof(f574,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f573,f297])).

fof(f573,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f572,f68])).

fof(f572,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f551,f277])).

fof(f551,plain,
    ( v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f371,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1940,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f695,f759])).

fof(f695,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f694,f64])).

fof(f694,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f693,f65])).

fof(f693,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f692,f66])).

fof(f692,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f691,f67])).

fof(f691,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f690,f69])).

fof(f690,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f689,f70])).

fof(f689,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f681,f68])).

fof(f681,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f518,f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f518,plain,
    ( ~ v5_pre_topc(sK6,sK4,sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(forward_demodulation,[],[f76,f74])).

fof(f76,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f1981,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f1964,f1955])).

fof(f1955,plain,(
    u1_struct_0(sK4) != k1_relat_1(sK6) ),
    inference(forward_demodulation,[],[f1954,f848])).

fof(f848,plain,(
    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) ),
    inference(resolution,[],[f759,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1954,plain,(
    u1_struct_0(sK4) != k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) ),
    inference(subsumption_resolution,[],[f1950,f759])).

fof(f1950,plain,
    ( u1_struct_0(sK4) != k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(resolution,[],[f1943,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1,sK6)
      | k1_relset_1(X1,X0,sK6) != X1
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f68,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f36,f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f1943,plain,(
    ~ sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6) ),
    inference(resolution,[],[f1942,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f1964,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f1961,f521])).

fof(f521,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | u1_struct_0(sK4) = k1_relat_1(sK6)
      | v1_funct_2(sK6,u1_struct_0(sK4),X0) ) ),
    inference(superposition,[],[f384,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f384,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),k1_xboole_0)
    | u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(superposition,[],[f69,f383])).

fof(f383,plain,
    ( k1_xboole_0 = u1_struct_0(sK5)
    | u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(resolution,[],[f377,f96])).

fof(f377,plain,
    ( sP0(u1_struct_0(sK4),u1_struct_0(sK5))
    | u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f376,f237])).

fof(f237,plain,(
    sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5)) ),
    inference(resolution,[],[f70,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f34,f41,f40,f39])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f376,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | sP0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f372,f69])).

fof(f372,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | sP0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5)) ),
    inference(superposition,[],[f235,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f235,plain,(
    k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k1_relat_1(sK6) ),
    inference(resolution,[],[f70,f90])).

fof(f1961,plain,(
    sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f1960,f1936])).

fof(f1936,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relat_1(sK6) ),
    inference(forward_demodulation,[],[f1935,f788])).

fof(f788,plain,(
    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6) ),
    inference(resolution,[],[f663,f90])).

fof(f663,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) ),
    inference(resolution,[],[f240,f617])).

fof(f617,plain,(
    r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(subsumption_resolution,[],[f616,f234])).

fof(f616,plain,
    ( r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f560,f83])).

fof(f560,plain,(
    v4_relat_1(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(resolution,[],[f371,f91])).

fof(f240,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK6),X0)
      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK5)))) ) ),
    inference(resolution,[],[f70,f104])).

fof(f1935,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6) ),
    inference(subsumption_resolution,[],[f1931,f663])).

fof(f1931,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) ),
    inference(resolution,[],[f1924,f175])).

fof(f1924,plain,(
    ~ sP3(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6) ),
    inference(resolution,[],[f1923,f101])).

fof(f1923,plain,(
    ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f1922,f1812])).

fof(f1812,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(subsumption_resolution,[],[f1811,f1623])).

fof(f1623,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f583,f663])).

fof(f583,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f582,f138])).

fof(f138,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f129,f64])).

fof(f129,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f65,f78])).

fof(f582,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f581,f229])).

fof(f229,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f128,f85])).

fof(f128,plain,(
    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f65,f77])).

fof(f581,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f580,f66])).

fof(f580,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f579,f67])).

fof(f579,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f578,f68])).

fof(f578,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f552,f277])).

fof(f552,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f371,f116])).

fof(f1811,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f653,f663])).

fof(f653,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f652,f64])).

fof(f652,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f651,f65])).

fof(f651,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f650,f66])).

fof(f650,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f649,f67])).

fof(f649,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f648,f69])).

fof(f648,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f647,f70])).

fof(f647,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f645,f68])).

fof(f645,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f513,f118])).

fof(f1922,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f1921,f1706])).

fof(f1706,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f589,f663])).

fof(f589,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f588,f138])).

fof(f588,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f587,f229])).

fof(f587,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f586,f66])).

fof(f586,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f585,f67])).

fof(f585,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f584,f68])).

fof(f584,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f553,f277])).

fof(f553,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f371,f115])).

fof(f1921,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f688,f663])).

fof(f688,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f687,f64])).

fof(f687,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f686,f65])).

fof(f686,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f685,f66])).

fof(f685,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f684,f67])).

fof(f684,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f683,f69])).

fof(f683,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f682,f70])).

fof(f682,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f680,f68])).

fof(f680,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f518,f117])).

fof(f1960,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK6)
    | sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(forward_demodulation,[],[f1959,f559])).

fof(f559,plain,(
    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) ),
    inference(resolution,[],[f371,f90])).

fof(f1959,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)
    | sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(subsumption_resolution,[],[f325,f561])).

fof(f561,plain,(
    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f371,f98])).

fof(f325,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)
    | sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(resolution,[],[f277,f94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (16868)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (16858)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (16872)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (16858)Refutation not found, incomplete strategy% (16858)------------------------------
% 0.21/0.50  % (16858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16858)Memory used [KB]: 10618
% 0.21/0.50  % (16858)Time elapsed: 0.092 s
% 0.21/0.50  % (16858)------------------------------
% 0.21/0.50  % (16858)------------------------------
% 0.21/0.51  % (16882)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (16881)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (16870)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (16876)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (16863)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (16864)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (16859)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (16865)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (16867)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (16880)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (16860)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (16864)Refutation not found, incomplete strategy% (16864)------------------------------
% 0.21/0.53  % (16864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16861)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (16874)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (16878)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (16864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16864)Memory used [KB]: 10746
% 0.21/0.53  % (16864)Time elapsed: 0.065 s
% 0.21/0.53  % (16864)------------------------------
% 0.21/0.53  % (16864)------------------------------
% 0.21/0.53  % (16862)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (16875)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (16877)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (16873)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (16866)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (16869)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (16879)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (16883)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (16871)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (16871)Refutation not found, incomplete strategy% (16871)------------------------------
% 0.21/0.56  % (16871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (16871)Memory used [KB]: 6268
% 0.21/0.56  % (16871)Time elapsed: 0.147 s
% 0.21/0.56  % (16871)------------------------------
% 0.21/0.56  % (16871)------------------------------
% 0.21/0.57  % (16869)Refutation not found, incomplete strategy% (16869)------------------------------
% 0.21/0.57  % (16869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (16869)Memory used [KB]: 10874
% 0.21/0.57  % (16869)Time elapsed: 0.159 s
% 0.21/0.57  % (16869)------------------------------
% 0.21/0.57  % (16869)------------------------------
% 2.15/0.68  % (16866)Refutation found. Thanks to Tanya!
% 2.15/0.68  % SZS status Theorem for theBenchmark
% 2.15/0.68  % SZS output start Proof for theBenchmark
% 2.15/0.68  fof(f1982,plain,(
% 2.15/0.68    $false),
% 2.15/0.68    inference(subsumption_resolution,[],[f1981,f1942])).
% 2.15/0.68  fof(f1942,plain,(
% 2.15/0.68    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1941,f1880])).
% 2.15/0.68  fof(f1880,plain,(
% 2.15/0.68    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1879,f1468])).
% 2.15/0.68  fof(f1468,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f571,f759])).
% 2.15/0.68  fof(f759,plain,(
% 2.15/0.68    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.15/0.68    inference(resolution,[],[f564,f269])).
% 2.15/0.68  fof(f269,plain,(
% 2.15/0.68    r1_tarski(k1_relat_1(sK6),u1_struct_0(sK4))),
% 2.15/0.68    inference(subsumption_resolution,[],[f268,f234])).
% 2.15/0.68  fof(f234,plain,(
% 2.15/0.68    v1_relat_1(sK6)),
% 2.15/0.68    inference(resolution,[],[f70,f89])).
% 2.15/0.68  fof(f89,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f30])).
% 2.15/0.68  fof(f30,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.68    inference(ennf_transformation,[],[f3])).
% 2.15/0.68  fof(f3,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.15/0.68  fof(f70,plain,(
% 2.15/0.68    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f51,plain,(
% 2.15/0.68    ((((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.15/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f46,f50,f49,f48,f47])).
% 2.15/0.68  fof(f47,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK4,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK4,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f48,plain,(
% 2.15/0.68    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK4,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK4,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(X2,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(X2,sK4,sK5)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f49,plain,(
% 2.15/0.68    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(X2,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(X2,sK4,sK5)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f50,plain,(
% 2.15/0.68    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(sK7))),
% 2.15/0.68    introduced(choice_axiom,[])).
% 2.15/0.68  fof(f46,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.15/0.68    inference(flattening,[],[f45])).
% 2.15/0.68  fof(f45,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.15/0.68    inference(nnf_transformation,[],[f20])).
% 2.15/0.68  fof(f20,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.15/0.68    inference(flattening,[],[f19])).
% 2.15/0.68  fof(f19,plain,(
% 2.15/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.15/0.68    inference(ennf_transformation,[],[f15])).
% 2.15/0.68  fof(f15,negated_conjecture,(
% 2.15/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.15/0.68    inference(negated_conjecture,[],[f14])).
% 2.15/0.68  fof(f14,conjecture,(
% 2.15/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 2.15/0.68  fof(f268,plain,(
% 2.15/0.68    r1_tarski(k1_relat_1(sK6),u1_struct_0(sK4)) | ~v1_relat_1(sK6)),
% 2.15/0.68    inference(resolution,[],[f236,f83])).
% 2.15/0.68  fof(f83,plain,(
% 2.15/0.68    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f54])).
% 2.15/0.68  fof(f54,plain,(
% 2.15/0.68    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.15/0.68    inference(nnf_transformation,[],[f28])).
% 2.15/0.68  fof(f28,plain,(
% 2.15/0.68    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.15/0.68    inference(ennf_transformation,[],[f2])).
% 2.15/0.68  fof(f2,axiom,(
% 2.15/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.15/0.68  fof(f236,plain,(
% 2.15/0.68    v4_relat_1(sK6,u1_struct_0(sK4))),
% 2.15/0.68    inference(resolution,[],[f70,f91])).
% 2.15/0.68  fof(f91,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f32])).
% 2.15/0.68  fof(f32,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.68    inference(ennf_transformation,[],[f18])).
% 2.15/0.68  fof(f18,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.15/0.68    inference(pure_predicate_removal,[],[f4])).
% 2.15/0.68  fof(f4,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.15/0.68  fof(f564,plain,(
% 2.15/0.68    ( ! [X0] : (~r1_tarski(k1_relat_1(sK6),X0) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))) )),
% 2.15/0.68    inference(resolution,[],[f371,f104])).
% 2.15/0.68  fof(f104,plain,(
% 2.15/0.68    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f38])).
% 2.15/0.68  fof(f38,plain,(
% 2.15/0.68    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.15/0.68    inference(flattening,[],[f37])).
% 2.15/0.68  fof(f37,plain,(
% 2.15/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.15/0.68    inference(ennf_transformation,[],[f6])).
% 2.15/0.68  fof(f6,axiom,(
% 2.15/0.68    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 2.15/0.68  fof(f371,plain,(
% 2.15/0.68    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.15/0.68    inference(forward_demodulation,[],[f73,f74])).
% 2.15/0.68  fof(f74,plain,(
% 2.15/0.68    sK6 = sK7),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f73,plain,(
% 2.15/0.68    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f571,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f570,f64])).
% 2.15/0.68  fof(f64,plain,(
% 2.15/0.68    v2_pre_topc(sK4)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f570,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f569,f65])).
% 2.15/0.68  fof(f65,plain,(
% 2.15/0.68    l1_pre_topc(sK4)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f569,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f568,f166])).
% 2.15/0.68  fof(f166,plain,(
% 2.15/0.68    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f157,f66])).
% 2.15/0.68  fof(f66,plain,(
% 2.15/0.68    v2_pre_topc(sK5)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f157,plain,(
% 2.15/0.68    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(sK5)),
% 2.15/0.68    inference(resolution,[],[f67,f78])).
% 2.15/0.68  fof(f78,plain,(
% 2.15/0.68    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f23])).
% 2.15/0.68  fof(f23,plain,(
% 2.15/0.68    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/0.68    inference(flattening,[],[f22])).
% 2.15/0.68  fof(f22,plain,(
% 2.15/0.68    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/0.68    inference(ennf_transformation,[],[f16])).
% 2.15/0.68  fof(f16,plain,(
% 2.15/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.15/0.68    inference(pure_predicate_removal,[],[f11])).
% 2.15/0.68  fof(f11,axiom,(
% 2.15/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 2.15/0.68  fof(f67,plain,(
% 2.15/0.68    l1_pre_topc(sK5)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f568,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f567,f297])).
% 2.15/0.68  fof(f297,plain,(
% 2.15/0.68    l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.15/0.68    inference(resolution,[],[f156,f85])).
% 2.15/0.68  fof(f85,plain,(
% 2.15/0.68    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f29])).
% 2.15/0.68  fof(f29,plain,(
% 2.15/0.68    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.15/0.68    inference(ennf_transformation,[],[f17])).
% 2.15/0.68  fof(f17,plain,(
% 2.15/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.15/0.68    inference(pure_predicate_removal,[],[f9])).
% 2.15/0.68  fof(f9,axiom,(
% 2.15/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 2.15/0.68  fof(f156,plain,(
% 2.15/0.68    m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))),
% 2.15/0.68    inference(resolution,[],[f67,f77])).
% 2.15/0.68  fof(f77,plain,(
% 2.15/0.68    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f21])).
% 2.15/0.68  fof(f21,plain,(
% 2.15/0.68    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.15/0.68    inference(ennf_transformation,[],[f10])).
% 2.15/0.68  fof(f10,axiom,(
% 2.15/0.68    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.15/0.68  fof(f567,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f566,f68])).
% 2.15/0.68  fof(f68,plain,(
% 2.15/0.68    v1_funct_1(sK6)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f566,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f550,f277])).
% 2.15/0.68  fof(f277,plain,(
% 2.15/0.68    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(forward_demodulation,[],[f72,f74])).
% 2.15/0.68  fof(f72,plain,(
% 2.15/0.68    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f550,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f371,f118])).
% 2.15/0.68  fof(f118,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(duplicate_literal_removal,[],[f108])).
% 2.15/0.68  fof(f108,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(equality_resolution,[],[f81])).
% 2.15/0.68  fof(f81,plain,(
% 2.15/0.68    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f53])).
% 2.15/0.68  fof(f53,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/0.68    inference(nnf_transformation,[],[f27])).
% 2.15/0.68  fof(f27,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/0.68    inference(flattening,[],[f26])).
% 2.15/0.68  fof(f26,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/0.68    inference(ennf_transformation,[],[f12])).
% 2.15/0.68  fof(f12,axiom,(
% 2.15/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.15/0.68  fof(f1879,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f660,f759])).
% 2.15/0.68  fof(f660,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f659,f64])).
% 2.15/0.68  fof(f659,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f658,f65])).
% 2.15/0.68  fof(f658,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f657,f66])).
% 2.15/0.68  fof(f657,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f656,f67])).
% 2.15/0.68  fof(f656,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f655,f69])).
% 2.15/0.68  fof(f69,plain,(
% 2.15/0.68    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f655,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f654,f70])).
% 2.15/0.68  fof(f654,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f646,f68])).
% 2.15/0.68  fof(f646,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f513,f116])).
% 2.15/0.68  fof(f116,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(duplicate_literal_removal,[],[f106])).
% 2.15/0.68  fof(f106,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(equality_resolution,[],[f79])).
% 2.15/0.68  fof(f79,plain,(
% 2.15/0.68    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f52])).
% 2.15/0.68  fof(f52,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/0.68    inference(nnf_transformation,[],[f25])).
% 2.15/0.68  fof(f25,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/0.68    inference(flattening,[],[f24])).
% 2.15/0.68  fof(f24,plain,(
% 2.15/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/0.68    inference(ennf_transformation,[],[f13])).
% 2.15/0.68  fof(f13,axiom,(
% 2.15/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 2.15/0.68  fof(f513,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,sK5) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.15/0.68    inference(forward_demodulation,[],[f75,f74])).
% 2.15/0.68  fof(f75,plain,(
% 2.15/0.68    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f1941,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1940,f1528])).
% 2.15/0.68  fof(f1528,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f577,f759])).
% 2.15/0.68  fof(f577,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f576,f64])).
% 2.15/0.68  fof(f576,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f575,f65])).
% 2.15/0.68  fof(f575,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f574,f166])).
% 2.15/0.68  fof(f574,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f573,f297])).
% 2.15/0.68  fof(f573,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f572,f68])).
% 2.15/0.68  fof(f572,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f551,f277])).
% 2.15/0.68  fof(f551,plain,(
% 2.15/0.68    v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f371,f117])).
% 2.15/0.68  fof(f117,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(duplicate_literal_removal,[],[f107])).
% 2.15/0.68  fof(f107,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(equality_resolution,[],[f82])).
% 2.15/0.68  fof(f82,plain,(
% 2.15/0.68    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f53])).
% 2.15/0.68  fof(f1940,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f695,f759])).
% 2.15/0.68  fof(f695,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f694,f64])).
% 2.15/0.68  fof(f694,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f693,f65])).
% 2.15/0.68  fof(f693,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f692,f66])).
% 2.15/0.68  fof(f692,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f691,f67])).
% 2.15/0.68  fof(f691,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f690,f69])).
% 2.15/0.68  fof(f690,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f689,f70])).
% 2.15/0.68  fof(f689,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f681,f68])).
% 2.15/0.68  fof(f681,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f518,f115])).
% 2.15/0.68  fof(f115,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(duplicate_literal_removal,[],[f105])).
% 2.15/0.68  fof(f105,plain,(
% 2.15/0.68    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(equality_resolution,[],[f80])).
% 2.15/0.68  fof(f80,plain,(
% 2.15/0.68    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f52])).
% 2.15/0.68  fof(f518,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,sK4,sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.15/0.68    inference(forward_demodulation,[],[f76,f74])).
% 2.15/0.68  fof(f76,plain,(
% 2.15/0.68    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)),
% 2.15/0.68    inference(cnf_transformation,[],[f51])).
% 2.15/0.68  fof(f1981,plain,(
% 2.15/0.68    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1964,f1955])).
% 2.15/0.68  fof(f1955,plain,(
% 2.15/0.68    u1_struct_0(sK4) != k1_relat_1(sK6)),
% 2.15/0.68    inference(forward_demodulation,[],[f1954,f848])).
% 2.15/0.68  fof(f848,plain,(
% 2.15/0.68    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)),
% 2.15/0.68    inference(resolution,[],[f759,f90])).
% 2.15/0.68  fof(f90,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f31])).
% 2.15/0.68  fof(f31,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.68    inference(ennf_transformation,[],[f5])).
% 2.15/0.68  fof(f5,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.15/0.68  fof(f1954,plain,(
% 2.15/0.68    u1_struct_0(sK4) != k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)),
% 2.15/0.68    inference(subsumption_resolution,[],[f1950,f759])).
% 2.15/0.68  fof(f1950,plain,(
% 2.15/0.68    u1_struct_0(sK4) != k1_relset_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.15/0.68    inference(resolution,[],[f1943,f175])).
% 2.15/0.68  fof(f175,plain,(
% 2.15/0.68    ( ! [X0,X1] : (sP3(X0,X1,sK6) | k1_relset_1(X1,X0,sK6) != X1 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.15/0.68    inference(resolution,[],[f68,f103])).
% 2.15/0.68  fof(f103,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f44])).
% 2.15/0.68  fof(f44,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (sP3(X1,X0,X2) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.15/0.68    inference(definition_folding,[],[f36,f43])).
% 2.15/0.68  fof(f43,plain,(
% 2.15/0.68    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 2.15/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.15/0.68  fof(f36,plain,(
% 2.15/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.15/0.68    inference(flattening,[],[f35])).
% 2.15/0.68  fof(f35,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.15/0.68    inference(ennf_transformation,[],[f8])).
% 2.15/0.68  fof(f8,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 2.15/0.68  fof(f1943,plain,(
% 2.15/0.68    ~sP3(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK4),sK6)),
% 2.15/0.68    inference(resolution,[],[f1942,f101])).
% 2.15/0.68  fof(f101,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (v1_funct_2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f63])).
% 2.15/0.68  fof(f63,plain,(
% 2.15/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 2.15/0.68    inference(rectify,[],[f62])).
% 2.15/0.68  fof(f62,plain,(
% 2.15/0.68    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 2.15/0.68    inference(nnf_transformation,[],[f43])).
% 2.15/0.68  fof(f1964,plain,(
% 2.15/0.68    u1_struct_0(sK4) = k1_relat_1(sK6) | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(resolution,[],[f1961,f521])).
% 2.15/0.68  fof(f521,plain,(
% 2.15/0.68    ( ! [X0,X1] : (~sP0(X1,X0) | u1_struct_0(sK4) = k1_relat_1(sK6) | v1_funct_2(sK6,u1_struct_0(sK4),X0)) )),
% 2.15/0.68    inference(superposition,[],[f384,f96])).
% 2.15/0.68  fof(f96,plain,(
% 2.15/0.68    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP0(X0,X1)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f61])).
% 2.15/0.68  fof(f61,plain,(
% 2.15/0.68    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 2.15/0.68    inference(nnf_transformation,[],[f39])).
% 2.15/0.68  fof(f39,plain,(
% 2.15/0.68    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 2.15/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.15/0.68  fof(f384,plain,(
% 2.15/0.68    v1_funct_2(sK6,u1_struct_0(sK4),k1_xboole_0) | u1_struct_0(sK4) = k1_relat_1(sK6)),
% 2.15/0.68    inference(superposition,[],[f69,f383])).
% 2.15/0.68  fof(f383,plain,(
% 2.15/0.68    k1_xboole_0 = u1_struct_0(sK5) | u1_struct_0(sK4) = k1_relat_1(sK6)),
% 2.15/0.68    inference(resolution,[],[f377,f96])).
% 2.15/0.68  fof(f377,plain,(
% 2.15/0.68    sP0(u1_struct_0(sK4),u1_struct_0(sK5)) | u1_struct_0(sK4) = k1_relat_1(sK6)),
% 2.15/0.68    inference(subsumption_resolution,[],[f376,f237])).
% 2.15/0.68  fof(f237,plain,(
% 2.15/0.68    sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5))),
% 2.15/0.68    inference(resolution,[],[f70,f98])).
% 2.15/0.68  fof(f98,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.68    inference(cnf_transformation,[],[f42])).
% 2.15/0.68  fof(f42,plain,(
% 2.15/0.68    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.68    inference(definition_folding,[],[f34,f41,f40,f39])).
% 2.15/0.68  fof(f40,plain,(
% 2.15/0.68    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 2.15/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.15/0.68  fof(f41,plain,(
% 2.15/0.68    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 2.15/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.15/0.68  fof(f34,plain,(
% 2.15/0.68    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.68    inference(flattening,[],[f33])).
% 2.15/0.68  fof(f33,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.68    inference(ennf_transformation,[],[f7])).
% 2.15/0.68  fof(f7,axiom,(
% 2.15/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.15/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.15/0.68  fof(f376,plain,(
% 2.15/0.68    u1_struct_0(sK4) = k1_relat_1(sK6) | sP0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f372,f69])).
% 2.15/0.68  fof(f372,plain,(
% 2.15/0.68    u1_struct_0(sK4) = k1_relat_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | sP0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~sP1(u1_struct_0(sK4),sK6,u1_struct_0(sK5))),
% 2.15/0.68    inference(superposition,[],[f235,f94])).
% 2.15/0.68  fof(f94,plain,(
% 2.15/0.68    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 2.15/0.68    inference(cnf_transformation,[],[f60])).
% 2.15/0.68  fof(f60,plain,(
% 2.15/0.68    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 2.15/0.68    inference(rectify,[],[f59])).
% 2.15/0.68  fof(f59,plain,(
% 2.15/0.68    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 2.15/0.68    inference(nnf_transformation,[],[f40])).
% 2.15/0.68  fof(f235,plain,(
% 2.15/0.68    k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k1_relat_1(sK6)),
% 2.15/0.68    inference(resolution,[],[f70,f90])).
% 2.15/0.68  fof(f1961,plain,(
% 2.15/0.68    sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1960,f1936])).
% 2.15/0.68  fof(f1936,plain,(
% 2.15/0.68    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relat_1(sK6)),
% 2.15/0.68    inference(forward_demodulation,[],[f1935,f788])).
% 2.15/0.68  fof(f788,plain,(
% 2.15/0.68    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6)),
% 2.15/0.68    inference(resolution,[],[f663,f90])).
% 2.15/0.68  fof(f663,plain,(
% 2.15/0.68    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))),
% 2.15/0.68    inference(resolution,[],[f240,f617])).
% 2.15/0.68  fof(f617,plain,(
% 2.15/0.68    r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f616,f234])).
% 2.15/0.68  fof(f616,plain,(
% 2.15/0.68    r1_tarski(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_relat_1(sK6)),
% 2.15/0.68    inference(resolution,[],[f560,f83])).
% 2.15/0.68  fof(f560,plain,(
% 2.15/0.68    v4_relat_1(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 2.15/0.68    inference(resolution,[],[f371,f91])).
% 2.15/0.68  fof(f240,plain,(
% 2.15/0.68    ( ! [X0] : (~r1_tarski(k1_relat_1(sK6),X0) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK5))))) )),
% 2.15/0.68    inference(resolution,[],[f70,f104])).
% 2.15/0.68  fof(f1935,plain,(
% 2.15/0.68    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6)),
% 2.15/0.68    inference(subsumption_resolution,[],[f1931,f663])).
% 2.15/0.68  fof(f1931,plain,(
% 2.15/0.68    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))),
% 2.15/0.68    inference(resolution,[],[f1924,f175])).
% 2.15/0.68  fof(f1924,plain,(
% 2.15/0.68    ~sP3(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6)),
% 2.15/0.68    inference(resolution,[],[f1923,f101])).
% 2.15/0.68  fof(f1923,plain,(
% 2.15/0.68    ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1922,f1812])).
% 2.15/0.68  fof(f1812,plain,(
% 2.15/0.68    ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1811,f1623])).
% 2.15/0.68  fof(f1623,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f583,f663])).
% 2.15/0.68  fof(f583,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f582,f138])).
% 2.15/0.68  fof(f138,plain,(
% 2.15/0.68    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f129,f64])).
% 2.15/0.68  fof(f129,plain,(
% 2.15/0.68    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f65,f78])).
% 2.15/0.68  fof(f582,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f581,f229])).
% 2.15/0.68  fof(f229,plain,(
% 2.15/0.68    l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(resolution,[],[f128,f85])).
% 2.15/0.68  fof(f128,plain,(
% 2.15/0.68    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 2.15/0.68    inference(resolution,[],[f65,f77])).
% 2.15/0.68  fof(f581,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f580,f66])).
% 2.15/0.68  fof(f580,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f579,f67])).
% 2.15/0.68  fof(f579,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f578,f68])).
% 2.15/0.68  fof(f578,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f552,f277])).
% 2.15/0.68  fof(f552,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(resolution,[],[f371,f116])).
% 2.15/0.68  fof(f1811,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f653,f663])).
% 2.15/0.68  fof(f653,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f652,f64])).
% 2.15/0.68  fof(f652,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f651,f65])).
% 2.15/0.68  fof(f651,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f650,f66])).
% 2.15/0.68  fof(f650,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f649,f67])).
% 2.15/0.68  fof(f649,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f648,f69])).
% 2.15/0.68  fof(f648,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f647,f70])).
% 2.15/0.68  fof(f647,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f645,f68])).
% 2.15/0.68  fof(f645,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f513,f118])).
% 2.15/0.68  fof(f1922,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f1921,f1706])).
% 2.15/0.68  fof(f1706,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f589,f663])).
% 2.15/0.68  fof(f589,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f588,f138])).
% 2.15/0.68  fof(f588,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f587,f229])).
% 2.15/0.68  fof(f587,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f586,f66])).
% 2.15/0.68  fof(f586,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f585,f67])).
% 2.15/0.68  fof(f585,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f584,f68])).
% 2.15/0.68  fof(f584,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(subsumption_resolution,[],[f553,f277])).
% 2.15/0.68  fof(f553,plain,(
% 2.15/0.68    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.15/0.68    inference(resolution,[],[f371,f115])).
% 2.15/0.68  fof(f1921,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f688,f663])).
% 2.15/0.68  fof(f688,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))),
% 2.15/0.68    inference(subsumption_resolution,[],[f687,f64])).
% 2.15/0.68  fof(f687,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f686,f65])).
% 2.15/0.68  fof(f686,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f685,f66])).
% 2.15/0.68  fof(f685,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f684,f67])).
% 2.15/0.68  fof(f684,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f683,f69])).
% 2.15/0.68  fof(f683,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f682,f70])).
% 2.15/0.68  fof(f682,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(subsumption_resolution,[],[f680,f68])).
% 2.15/0.68  fof(f680,plain,(
% 2.15/0.68    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 2.15/0.68    inference(resolution,[],[f518,f117])).
% 2.15/0.68  fof(f1960,plain,(
% 2.15/0.68    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK6) | sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(forward_demodulation,[],[f1959,f559])).
% 2.15/0.68  fof(f559,plain,(
% 2.15/0.68    k1_relat_1(sK6) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6)),
% 2.15/0.68    inference(resolution,[],[f371,f90])).
% 2.15/0.68  fof(f1959,plain,(
% 2.15/0.68    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) | sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(subsumption_resolution,[],[f325,f561])).
% 2.15/0.68  fof(f561,plain,(
% 2.15/0.68    sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(resolution,[],[f371,f98])).
% 2.15/0.68  fof(f325,plain,(
% 2.15/0.68    u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK6) | sP0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) | ~sP1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.15/0.68    inference(resolution,[],[f277,f94])).
% 2.15/0.68  % SZS output end Proof for theBenchmark
% 2.15/0.68  % (16866)------------------------------
% 2.15/0.68  % (16866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (16866)Termination reason: Refutation
% 2.15/0.68  
% 2.15/0.68  % (16866)Memory used [KB]: 2686
% 2.15/0.68  % (16866)Time elapsed: 0.272 s
% 2.15/0.68  % (16866)------------------------------
% 2.15/0.68  % (16866)------------------------------
% 2.15/0.68  % (16867)Refutation not found, incomplete strategy% (16867)------------------------------
% 2.15/0.68  % (16867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (16867)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.68  
% 2.15/0.68  % (16867)Memory used [KB]: 6268
% 2.15/0.68  % (16867)Time elapsed: 0.284 s
% 2.15/0.68  % (16867)------------------------------
% 2.15/0.68  % (16867)------------------------------
% 2.15/0.69  % (16857)Success in time 0.336 s
%------------------------------------------------------------------------------
