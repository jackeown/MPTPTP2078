%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:31 EST 2020

% Result     : Theorem 3.69s
% Output     : Refutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  426 (4769 expanded)
%              Number of leaves         :   38 (1587 expanded)
%              Depth                    :   30
%              Number of atoms          : 2460 (53899 expanded)
%              Number of equality atoms :  101 (5590 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4757,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f140,f321,f349,f376,f378,f694,f787,f911,f1045,f1077,f1098,f1266,f2053,f2078,f2277,f2279,f2293,f2296,f2298,f2484,f3208,f3221,f3316,f3753,f3836,f3839,f4074,f4083,f4131,f4438,f4756])).

fof(f4756,plain,
    ( spl4_1
    | ~ spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f4755])).

fof(f4755,plain,
    ( $false
    | spl4_1
    | ~ spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4754,f143])).

fof(f143,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f76,f79])).

fof(f79,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f61,f60,f59,f58])).

fof(f58,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f4754,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4753,f3361])).

fof(f3361,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f3330,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3330,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f141,f493])).

fof(f493,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl4_34
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f141,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f78,f79])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f62])).

fof(f4753,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4752,f3559])).

fof(f3559,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3558,f180])).

fof(f180,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f108,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3558,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_34 ),
    inference(resolution,[],[f3431,f121])).

fof(f121,plain,(
    ! [X1] :
      ( ~ v4_relat_1(X1,k1_relat_1(X1))
      | v1_partfun1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f3431,plain,
    ( ! [X0] : v4_relat_1(sK2,X0)
    | ~ spl4_34 ),
    inference(resolution,[],[f3361,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f110,f122])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f4752,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(resolution,[],[f4726,f797])).

fof(f797,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k1_xboole_0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f393,f122])).

fof(f393,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | v1_funct_2(X0,k1_relat_1(X0),X1)
      | ~ v1_funct_1(X0) ) ),
    inference(equality_resolution,[],[f281])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f112,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f4726,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | spl4_1
    | ~ spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(superposition,[],[f4724,f4465])).

fof(f4465,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4464,f3431])).

fof(f4464,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f4463,f180])).

fof(f4463,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f4462,f199])).

fof(f199,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f110,f75])).

fof(f4462,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v4_relat_1(sK2,u1_struct_0(sK0))
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(resolution,[],[f478,f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X2)
      | X1 = X2
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v1_partfun1(X0,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f102,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f478,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl4_31
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f4724,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4723,f69])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f4723,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4722,f70])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f4722,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4721,f74])).

fof(f74,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f4721,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4720,f75])).

fof(f4720,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4719,f143])).

fof(f4719,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4718,f133])).

fof(f133,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4718,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4716,f3361])).

fof(f4716,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(resolution,[],[f3490,f313])).

fof(f313,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl4_22
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f3490,plain,
    ( ! [X6,X7] :
        ( ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f3489,f122])).

fof(f3489,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3488,f71])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f3488,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3443,f72])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f3443,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_34 ),
    inference(superposition,[],[f130,f493])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f4438,plain,
    ( spl4_1
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f4437])).

fof(f4437,plain,
    ( $false
    | spl4_1
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4436,f69])).

fof(f4436,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4435,f70])).

fof(f4435,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4434,f143])).

fof(f4434,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4433,f133])).

fof(f4433,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4432,f3840])).

fof(f3840,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f74,f481])).

fof(f481,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl4_32
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f4432,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4424,f3361])).

fof(f4424,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_22
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(resolution,[],[f4353,f4132])).

fof(f4132,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_22
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f313,f481])).

fof(f4353,plain,
    ( ! [X14,X15] :
        ( ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_1(X14)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(duplicate_literal_removal,[],[f4352])).

fof(f4352,plain,
    ( ! [X14,X15] :
        ( ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f4201,f3846])).

fof(f3846,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f493,f481])).

fof(f4201,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f4200,f122])).

fof(f4200,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(duplicate_literal_removal,[],[f4199])).

fof(f4199,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f4198,f3846])).

fof(f4198,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f4197,f71])).

fof(f4197,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f4142,f72])).

fof(f4142,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(X14,X15,sK1)
        | ~ v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0)))
        | ~ v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15) )
    | ~ spl4_32 ),
    inference(superposition,[],[f130,f481])).

fof(f4131,plain,
    ( spl4_20
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f4130])).

fof(f4130,plain,
    ( $false
    | spl4_20
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4129,f3840])).

fof(f4129,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | spl4_20
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f4077,f3846])).

fof(f4077,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl4_20
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f307,f481])).

fof(f307,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl4_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f4083,plain,
    ( ~ spl4_32
    | spl4_129
    | ~ spl4_137 ),
    inference(avatar_contradiction_clause,[],[f4082])).

fof(f4082,plain,
    ( $false
    | ~ spl4_32
    | spl4_129
    | ~ spl4_137 ),
    inference(subsumption_resolution,[],[f4081,f2123])).

fof(f2123,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_129 ),
    inference(avatar_component_clause,[],[f2090])).

fof(f2090,plain,
    ( spl4_129
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).

fof(f4081,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_137 ),
    inference(forward_demodulation,[],[f2499,f481])).

fof(f2499,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_137 ),
    inference(avatar_component_clause,[],[f2490])).

fof(f2490,plain,
    ( spl4_137
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).

fof(f4074,plain,
    ( ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(avatar_contradiction_clause,[],[f4073])).

fof(f4073,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4072,f3840])).

fof(f4072,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(forward_demodulation,[],[f4071,f481])).

fof(f4071,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4070,f4064])).

fof(f4064,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(forward_demodulation,[],[f4063,f481])).

fof(f4063,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4062,f3361])).

fof(f4062,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4061,f3331])).

fof(f3331,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f142,f493])).

fof(f142,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f77,f79])).

fof(f77,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f4061,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4060,f143])).

fof(f4060,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_32
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4059,f3840])).

fof(f4059,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f4058,f70])).

fof(f4058,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_56
    | spl4_137 ),
    inference(subsumption_resolution,[],[f3798,f69])).

fof(f3798,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_56
    | spl4_137 ),
    inference(resolution,[],[f910,f2491])).

fof(f2491,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_137 ),
    inference(avatar_component_clause,[],[f2490])).

fof(f910,plain,
    ( ! [X10,X11] :
        ( v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f909])).

fof(f909,plain,
    ( spl4_56
  <=> ! [X11,X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)
        | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f4070,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f4069,f481])).

fof(f4069,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4068,f69])).

fof(f4068,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4067,f70])).

fof(f4067,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4066,f3361])).

fof(f4066,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f4065,f143])).

fof(f4065,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3784,f3840])).

fof(f3784,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3764,f138])).

fof(f138,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f3764,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_34 ),
    inference(resolution,[],[f3487,f75])).

fof(f3487,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X4,X5,sK1)
        | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f3486,f122])).

fof(f3486,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k1_xboole_0)))
        | ~ v5_pre_topc(X4,X5,sK1)
        | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3485,f71])).

fof(f3485,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k1_xboole_0)))
        | ~ v5_pre_topc(X4,X5,sK1)
        | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3442,f72])).

fof(f3442,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k1_xboole_0)))
        | ~ v5_pre_topc(X4,X5,sK1)
        | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_34 ),
    inference(superposition,[],[f129,f493])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
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
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f3839,plain,
    ( spl4_31
    | spl4_32 ),
    inference(avatar_split_clause,[],[f3838,f480,f477])).

fof(f3838,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3837,f143])).

fof(f3837,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f2299,f74])).

fof(f2299,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f75,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f3836,plain,
    ( ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f3835])).

fof(f3835,plain,
    ( $false
    | ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3834,f143])).

fof(f3834,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3833,f3361])).

fof(f3833,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3830,f3559])).

fof(f3830,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(resolution,[],[f3797,f797])).

fof(f3797,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3796,f3431])).

fof(f3796,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_1
    | spl4_22
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(superposition,[],[f3790,f2326])).

fof(f2326,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f2325,f180])).

fof(f2325,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f2324,f199])).

fof(f2324,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = X0
        | ~ v4_relat_1(sK2,u1_struct_0(sK0))
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(resolution,[],[f478,f238])).

fof(f3790,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3789,f69])).

fof(f3789,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3788,f70])).

fof(f3788,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3787,f74])).

fof(f3787,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3786,f3361])).

fof(f3786,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3785,f143])).

fof(f3785,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | spl4_22
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3784,f2282])).

fof(f2282,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f312])).

fof(f3753,plain,
    ( spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f3752])).

fof(f3752,plain,
    ( $false
    | spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3751,f143])).

fof(f3751,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3750,f3361])).

fof(f3750,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3747,f3559])).

fof(f3747,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(resolution,[],[f3737,f797])).

fof(f3737,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f3736,f3431])).

fof(f3736,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_20
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(superposition,[],[f3735,f2326])).

fof(f3735,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | spl4_20
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f307,f493])).

fof(f3316,plain,
    ( ~ spl4_31
    | ~ spl4_162 ),
    inference(avatar_contradiction_clause,[],[f3315])).

fof(f3315,plain,
    ( $false
    | ~ spl4_31
    | ~ spl4_162 ),
    inference(subsumption_resolution,[],[f3314,f74])).

fof(f3314,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_31
    | ~ spl4_162 ),
    inference(subsumption_resolution,[],[f3309,f478])).

fof(f3309,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_162 ),
    inference(resolution,[],[f3220,f75])).

fof(f3220,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X3)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1)) )
    | ~ spl4_162 ),
    inference(avatar_component_clause,[],[f3219])).

fof(f3219,plain,
    ( spl4_162
  <=> ! [X3] :
        ( ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ v1_partfun1(sK2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f3221,plain,
    ( spl4_162
    | spl4_27
    | ~ spl4_1
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f3217,f489,f477,f132,f343,f3219])).

fof(f343,plain,
    ( spl4_27
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f489,plain,
    ( spl4_33
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f3217,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X3) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3216,f110])).

fof(f3216,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3215,f199])).

fof(f3215,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3)
        | ~ v4_relat_1(sK2,u1_struct_0(sK0)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3214,f478])).

fof(f3214,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3)
        | ~ v1_partfun1(sK2,u1_struct_0(sK0))
        | ~ v4_relat_1(sK2,u1_struct_0(sK0)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3213,f71])).

fof(f3213,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3)
        | ~ v1_partfun1(sK2,u1_struct_0(sK0))
        | ~ v4_relat_1(sK2,u1_struct_0(sK0)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3212,f72])).

fof(f3212,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3)
        | ~ v1_partfun1(sK2,u1_struct_0(sK0))
        | ~ v4_relat_1(sK2,u1_struct_0(sK0)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3211,f74])).

fof(f3211,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3)
        | ~ v1_partfun1(sK2,u1_struct_0(sK0))
        | ~ v4_relat_1(sK2,u1_struct_0(sK0)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3139,f143])).

fof(f3139,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v1_funct_2(sK2,X3,u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X3)
        | ~ v4_relat_1(sK2,X3)
        | ~ v1_partfun1(sK2,u1_struct_0(sK0))
        | ~ v4_relat_1(sK2,u1_struct_0(sK0)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(resolution,[],[f2576,f2381])).

fof(f2381,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X1)
        | ~ v4_relat_1(sK2,X1) )
    | ~ spl4_31 ),
    inference(superposition,[],[f75,f2326])).

fof(f2576,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X14))))
        | ~ v5_pre_topc(X13,sK0,X14)
        | v5_pre_topc(X13,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X14)
        | ~ v1_funct_2(X13,X12,u1_struct_0(X14))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,u1_struct_0(X14))))
        | ~ v1_funct_2(X13,u1_struct_0(sK0),u1_struct_0(X14))
        | ~ l1_pre_topc(X14)
        | ~ v2_pre_topc(X14)
        | ~ v1_partfun1(sK2,X12)
        | ~ v4_relat_1(sK2,X12) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2575,f69])).

fof(f2575,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,u1_struct_0(X14))))
        | ~ v5_pre_topc(X13,sK0,X14)
        | v5_pre_topc(X13,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X14)
        | ~ v1_funct_2(X13,X12,u1_struct_0(X14))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X14))))
        | ~ v1_funct_2(X13,u1_struct_0(sK0),u1_struct_0(X14))
        | ~ l1_pre_topc(X14)
        | ~ v2_pre_topc(X14)
        | ~ v2_pre_topc(sK0)
        | ~ v1_partfun1(sK2,X12)
        | ~ v4_relat_1(sK2,X12) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2543,f70])).

fof(f2543,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,u1_struct_0(X14))))
        | ~ v5_pre_topc(X13,sK0,X14)
        | v5_pre_topc(X13,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X14)
        | ~ v1_funct_2(X13,X12,u1_struct_0(X14))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X14))))
        | ~ v1_funct_2(X13,u1_struct_0(sK0),u1_struct_0(X14))
        | ~ l1_pre_topc(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v1_partfun1(sK2,X12)
        | ~ v4_relat_1(sK2,X12) )
    | ~ spl4_33 ),
    inference(superposition,[],[f127,f1411])).

fof(f1411,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1410,f180])).

fof(f1410,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1409,f200])).

fof(f200,plain,(
    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f110,f141])).

fof(f1409,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_33 ),
    inference(resolution,[],[f490,f238])).

fof(f490,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f489])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
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
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f3208,plain,
    ( spl4_1
    | ~ spl4_27
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f3207])).

fof(f3207,plain,
    ( $false
    | spl4_1
    | ~ spl4_27
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3206,f478])).

fof(f3206,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3201,f74])).

fof(f3201,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(resolution,[],[f3167,f75])).

fof(f3167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_partfun1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3166,f110])).

fof(f3166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3165,f71])).

fof(f3165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3164,f72])).

fof(f3164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3163,f74])).

fof(f3163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3162,f75])).

fof(f3162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3161,f143])).

fof(f3161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f3154,f133])).

fof(f3154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(resolution,[],[f2578,f344])).

fof(f344,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f343])).

fof(f2578,plain,
    ( ! [X17,X15,X16] :
        ( ~ v5_pre_topc(X16,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X17)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,u1_struct_0(X17))))
        | v5_pre_topc(X16,sK0,X17)
        | ~ v1_funct_2(X16,X15,u1_struct_0(X17))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))
        | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ v1_partfun1(sK2,X15)
        | ~ v4_relat_1(sK2,X15) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2577,f69])).

fof(f2577,plain,
    ( ! [X17,X15,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,u1_struct_0(X17))))
        | ~ v5_pre_topc(X16,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X17)
        | v5_pre_topc(X16,sK0,X17)
        | ~ v1_funct_2(X16,X15,u1_struct_0(X17))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))
        | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ v2_pre_topc(sK0)
        | ~ v1_partfun1(sK2,X15)
        | ~ v4_relat_1(sK2,X15) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2544,f70])).

fof(f2544,plain,
    ( ! [X17,X15,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,u1_struct_0(X17))))
        | ~ v5_pre_topc(X16,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X17)
        | v5_pre_topc(X16,sK0,X17)
        | ~ v1_funct_2(X16,X15,u1_struct_0(X17))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17))))
        | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17))
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v1_partfun1(sK2,X15)
        | ~ v4_relat_1(sK2,X15) )
    | ~ spl4_33 ),
    inference(superposition,[],[f128,f1411])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
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
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f2484,plain,
    ( spl4_25
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f2483])).

fof(f2483,plain,
    ( $false
    | spl4_25
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2482,f200])).

fof(f2482,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl4_25
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2480,f490])).

fof(f2480,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl4_25
    | ~ spl4_31 ),
    inference(resolution,[],[f2380,f338])).

fof(f338,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl4_25
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f2380,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_31 ),
    inference(superposition,[],[f74,f2326])).

fof(f2298,plain,(
    spl4_74 ),
    inference(avatar_contradiction_clause,[],[f2297])).

fof(f2297,plain,
    ( $false
    | spl4_74 ),
    inference(subsumption_resolution,[],[f1260,f142])).

fof(f1260,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_74 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f1259,plain,
    ( spl4_74
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f2296,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_74
    | spl4_2
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f2295,f343,f135,f1259,f340,f337,f334,f331])).

fof(f331,plain,
    ( spl4_23
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f334,plain,
    ( spl4_24
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f340,plain,
    ( spl4_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f135,plain,
    ( spl4_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2295,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_2
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f2294,f2280])).

fof(f2280,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2 ),
    inference(forward_demodulation,[],[f136,f79])).

fof(f136,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f2294,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f2141,f344])).

fof(f2141,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f2140,f71])).

fof(f2140,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f2139,f72])).

fof(f2139,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f977,f143])).

fof(f977,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f141,f129])).

fof(f2293,plain,
    ( ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_74
    | ~ spl4_22
    | spl4_2 ),
    inference(avatar_split_clause,[],[f2292,f135,f312,f1259,f309,f306,f303,f300])).

fof(f300,plain,
    ( spl4_18
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f303,plain,
    ( spl4_19
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f309,plain,
    ( spl4_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f2292,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f2153,f2280])).

fof(f2153,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f2152,f69])).

fof(f2152,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2151,f70])).

fof(f2151,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f975,f143])).

fof(f975,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f141,f127])).

fof(f2279,plain,
    ( spl4_2
    | ~ spl4_32
    | ~ spl4_129 ),
    inference(avatar_contradiction_clause,[],[f2278])).

fof(f2278,plain,
    ( $false
    | spl4_2
    | ~ spl4_32
    | ~ spl4_129 ),
    inference(subsumption_resolution,[],[f2091,f2245])).

fof(f2245,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f2244,f79])).

fof(f2244,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f136,f481])).

fof(f2091,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_129 ),
    inference(avatar_component_clause,[],[f2090])).

fof(f2277,plain,
    ( ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f2274])).

fof(f2274,plain,
    ( $false
    | ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(resolution,[],[f2271,f1335])).

fof(f1335,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1334,f180])).

fof(f1334,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_32 ),
    inference(resolution,[],[f1327,f121])).

fof(f1327,plain,
    ( ! [X0] : v4_relat_1(sK2,X0)
    | ~ spl4_32 ),
    inference(resolution,[],[f1303,f203])).

fof(f1303,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1278,f122])).

fof(f1278,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f75,f481])).

fof(f2271,plain,
    ( ! [X0] : ~ v1_partfun1(sK2,X0)
    | ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2270,f2042])).

fof(f2042,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2038,f1303])).

fof(f2038,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(superposition,[],[f2034,f122])).

fof(f2034,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(sK2,X0,X1)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(equality_resolution,[],[f1809])).

fof(f1809,plain,
    ( ! [X6,X7,X5] :
        ( X5 != X6
        | v1_funct_2(sK2,X6,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_partfun1(sK2,X5) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1806,f143])).

fof(f1806,plain,
    ( ! [X6,X7,X5] :
        ( X5 != X6
        | v1_funct_2(sK2,X6,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X5) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(superposition,[],[f281,f1783])).

fof(f1783,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(resolution,[],[f1557,f1335])).

fof(f1557,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK2,X1)
        | X0 = X1
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(superposition,[],[f1412,f1412])).

fof(f1412,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1411,f1327])).

fof(f2270,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2269,f1277])).

fof(f1277,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f74,f481])).

fof(f2269,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2268,f143])).

fof(f2268,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2267,f1303])).

fof(f2267,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2264,f138])).

fof(f2264,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,X0,k1_xboole_0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(resolution,[],[f1718,f2149])).

fof(f2149,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f343])).

fof(f1718,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v5_pre_topc(X1,sK0,sK1)
        | ~ v1_funct_2(X1,X0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),k1_xboole_0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1717,f69])).

fof(f1717,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,k1_xboole_0)
        | ~ v5_pre_topc(X1,sK0,sK1)
        | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),k1_xboole_0)
        | ~ v2_pre_topc(sK0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1710,f70])).

fof(f1710,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,k1_xboole_0)
        | ~ v5_pre_topc(X1,sK0,sK1)
        | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(superposition,[],[f1362,f1412])).

fof(f1362,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_32 ),
    inference(duplicate_literal_removal,[],[f1361])).

fof(f1361,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1360,f122])).

fof(f1360,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1359,f122])).

fof(f1359,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1358,f71])).

fof(f1358,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1339,f72])).

fof(f1339,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,sK1)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_32 ),
    inference(superposition,[],[f127,f481])).

fof(f2078,plain,
    ( spl4_1
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f2077])).

fof(f2077,plain,
    ( $false
    | spl4_1
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2076,f69])).

fof(f2076,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2075,f70])).

fof(f2075,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2074,f1277])).

fof(f2074,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2073,f133])).

fof(f2073,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2070,f490])).

fof(f2070,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(resolution,[],[f2058,f344])).

fof(f2058,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(sK2,X0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2057,f143])).

fof(f2057,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | v5_pre_topc(sK2,X0,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2055,f1303])).

fof(f2055,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | v5_pre_topc(sK2,X0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(resolution,[],[f2042,f1370])).

fof(f1370,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)
        | ~ v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1)
        | v5_pre_topc(X6,X7,sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_32 ),
    inference(duplicate_literal_removal,[],[f1369])).

fof(f1369,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1)
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1368,f122])).

fof(f1368,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1)
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1367,f122])).

fof(f1367,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)))
        | ~ v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1)
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1366,f71])).

fof(f1366,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)))
        | ~ v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1)
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1341,f72])).

fof(f1341,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)))
        | ~ v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1)
        | v5_pre_topc(X6,X7,sK1)
        | ~ v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0)))
        | ~ v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl4_32 ),
    inference(superposition,[],[f128,f481])).

fof(f2053,plain,
    ( spl4_25
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f2050])).

fof(f2050,plain,
    ( $false
    | spl4_25
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(resolution,[],[f2043,f1335])).

fof(f2043,plain,
    ( ! [X0] : ~ v1_partfun1(sK2,X0)
    | spl4_25
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f2042,f1563])).

fof(f1563,plain,
    ( ! [X6] :
        ( ~ v1_funct_2(sK2,X6,k1_xboole_0)
        | ~ v1_partfun1(sK2,X6) )
    | spl4_25
    | ~ spl4_32
    | ~ spl4_33 ),
    inference(superposition,[],[f1323,f1412])).

fof(f1323,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl4_25
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f338,f481])).

fof(f1266,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_74
    | spl4_27
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f1265,f135,f343,f1259,f340,f337,f334,f331])).

fof(f1265,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1264,f71])).

fof(f1264,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1263,f72])).

fof(f1263,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1262,f143])).

fof(f1262,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f705,f145])).

fof(f145,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f139,f79])).

fof(f139,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f705,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f141,f130])).

fof(f1098,plain,
    ( spl4_33
    | spl4_34 ),
    inference(avatar_split_clause,[],[f1097,f492,f489])).

fof(f1097,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f1096,f143])).

fof(f1096,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f978,f142])).

fof(f978,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f141,f125])).

fof(f1077,plain,
    ( spl4_26
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | spl4_26
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1075,f1069])).

fof(f1069,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1047,f122])).

fof(f1047,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f75,f481])).

fof(f1075,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_26
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1058,f122])).

fof(f1058,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | spl4_26
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f341,f481])).

fof(f341,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f340])).

fof(f1045,plain,
    ( spl4_26
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f1044])).

fof(f1044,plain,
    ( $false
    | spl4_26
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1041,f478])).

fof(f1041,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | spl4_26
    | ~ spl4_33 ),
    inference(resolution,[],[f1031,f75])).

fof(f1031,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X6) )
    | spl4_26
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1008,f110])).

fof(f1008,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X6)
        | ~ v4_relat_1(sK2,X6) )
    | spl4_26
    | ~ spl4_33 ),
    inference(superposition,[],[f341,f992])).

fof(f992,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f991,f180])).

fof(f991,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f989,f200])).

fof(f989,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_relat_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_33 ),
    inference(resolution,[],[f490,f238])).

fof(f911,plain,
    ( ~ spl4_18
    | ~ spl4_19
    | spl4_56
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f907,f492,f909,f303,f300])).

fof(f907,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11) )
    | ~ spl4_34 ),
    inference(duplicate_literal_removal,[],[f906])).

fof(f906,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11) )
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f905,f122])).

fof(f905,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k1_xboole_0)))
        | ~ v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11) )
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f867,f122])).

fof(f867,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)))
        | ~ v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0)
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k1_xboole_0)))
        | ~ v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11) )
    | ~ spl4_34 ),
    inference(superposition,[],[f127,f493])).

fof(f787,plain,
    ( ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_21
    | spl4_22
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f786,f135,f312,f309,f306,f303,f300])).

fof(f786,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f785,f69])).

fof(f785,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f784,f70])).

fof(f784,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f783,f143])).

fof(f783,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f782,f142])).

fof(f782,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f703,f145])).

fof(f703,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f141,f128])).

fof(f694,plain,
    ( spl4_21
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | spl4_21
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f692,f686])).

fof(f686,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f671,f122])).

fof(f671,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f141,f493])).

fof(f692,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_21
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f677,f122])).

fof(f677,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl4_21
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f310,f493])).

fof(f310,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f309])).

fof(f378,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl4_24 ),
    inference(subsumption_resolution,[],[f374,f70])).

fof(f374,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_24 ),
    inference(resolution,[],[f197,f335])).

fof(f335,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f334])).

fof(f197,plain,(
    ! [X1] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f98,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f376,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f373,f72])).

fof(f373,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_19 ),
    inference(resolution,[],[f197,f304])).

fof(f304,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f303])).

fof(f349,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl4_23 ),
    inference(subsumption_resolution,[],[f347,f69])).

fof(f347,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_23 ),
    inference(subsumption_resolution,[],[f346,f70])).

fof(f346,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_23 ),
    inference(resolution,[],[f332,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f332,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f331])).

fof(f321,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f319,f71])).

fof(f319,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_18 ),
    inference(subsumption_resolution,[],[f318,f72])).

fof(f318,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl4_18 ),
    inference(resolution,[],[f301,f86])).

fof(f301,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f300])).

fof(f140,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f80,f135,f132])).

fof(f80,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f137,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f135,f132])).

fof(f81,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (31411)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (31402)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (31407)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (31410)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (31410)Refutation not found, incomplete strategy% (31410)------------------------------
% 0.20/0.48  % (31410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31410)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31410)Memory used [KB]: 1791
% 0.20/0.48  % (31410)Time elapsed: 0.065 s
% 0.20/0.48  % (31410)------------------------------
% 0.20/0.48  % (31410)------------------------------
% 0.20/0.48  % (31401)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (31406)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (31405)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (31400)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (31404)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (31414)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (31415)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (31413)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (31417)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (31399)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (31398)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31417)Refutation not found, incomplete strategy% (31417)------------------------------
% 0.20/0.50  % (31417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31417)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (31417)Memory used [KB]: 10618
% 0.20/0.50  % (31417)Time elapsed: 0.097 s
% 0.20/0.50  % (31417)------------------------------
% 0.20/0.50  % (31417)------------------------------
% 0.20/0.50  % (31397)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (31416)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (31398)Refutation not found, incomplete strategy% (31398)------------------------------
% 0.20/0.50  % (31398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31398)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (31398)Memory used [KB]: 10746
% 0.20/0.50  % (31398)Time elapsed: 0.097 s
% 0.20/0.50  % (31398)------------------------------
% 0.20/0.50  % (31398)------------------------------
% 0.20/0.50  % (31409)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31408)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (31412)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (31400)Refutation not found, incomplete strategy% (31400)------------------------------
% 0.20/0.51  % (31400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31400)Memory used [KB]: 10874
% 0.20/0.51  % (31400)Time elapsed: 0.089 s
% 0.20/0.51  % (31400)------------------------------
% 0.20/0.51  % (31400)------------------------------
% 0.20/0.51  % (31403)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 3.69/0.82  % (31399)Refutation found. Thanks to Tanya!
% 3.69/0.82  % SZS status Theorem for theBenchmark
% 3.69/0.82  % SZS output start Proof for theBenchmark
% 3.69/0.82  fof(f4757,plain,(
% 3.69/0.82    $false),
% 3.69/0.82    inference(avatar_sat_refutation,[],[f137,f140,f321,f349,f376,f378,f694,f787,f911,f1045,f1077,f1098,f1266,f2053,f2078,f2277,f2279,f2293,f2296,f2298,f2484,f3208,f3221,f3316,f3753,f3836,f3839,f4074,f4083,f4131,f4438,f4756])).
% 3.69/0.82  fof(f4756,plain,(
% 3.69/0.82    spl4_1 | ~spl4_22 | ~spl4_31 | ~spl4_34),
% 3.69/0.82    inference(avatar_contradiction_clause,[],[f4755])).
% 3.69/0.82  fof(f4755,plain,(
% 3.69/0.82    $false | (spl4_1 | ~spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4754,f143])).
% 3.69/0.82  fof(f143,plain,(
% 3.69/0.82    v1_funct_1(sK2)),
% 3.69/0.82    inference(forward_demodulation,[],[f76,f79])).
% 3.69/0.82  fof(f79,plain,(
% 3.69/0.82    sK2 = sK3),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f62,plain,(
% 3.69/0.82    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.69/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f61,f60,f59,f58])).
% 3.69/0.82  fof(f58,plain,(
% 3.69/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.69/0.82    introduced(choice_axiom,[])).
% 3.69/0.82  fof(f59,plain,(
% 3.69/0.82    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.69/0.82    introduced(choice_axiom,[])).
% 3.69/0.82  fof(f60,plain,(
% 3.69/0.82    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 3.69/0.82    introduced(choice_axiom,[])).
% 3.69/0.82  fof(f61,plain,(
% 3.69/0.82    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 3.69/0.82    introduced(choice_axiom,[])).
% 3.69/0.82  fof(f57,plain,(
% 3.69/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.69/0.82    inference(flattening,[],[f56])).
% 3.69/0.82  fof(f56,plain,(
% 3.69/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.69/0.82    inference(nnf_transformation,[],[f28])).
% 3.69/0.82  fof(f28,plain,(
% 3.69/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.69/0.82    inference(flattening,[],[f27])).
% 3.69/0.82  fof(f27,plain,(
% 3.69/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.69/0.82    inference(ennf_transformation,[],[f23])).
% 3.69/0.82  fof(f23,negated_conjecture,(
% 3.69/0.82    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.69/0.82    inference(negated_conjecture,[],[f22])).
% 3.69/0.82  fof(f22,conjecture,(
% 3.69/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.69/0.82  fof(f76,plain,(
% 3.69/0.82    v1_funct_1(sK3)),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f4754,plain,(
% 3.69/0.82    ~v1_funct_1(sK2) | (spl4_1 | ~spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4753,f3361])).
% 3.69/0.82  fof(f3361,plain,(
% 3.69/0.82    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_34),
% 3.69/0.82    inference(forward_demodulation,[],[f3330,f122])).
% 3.69/0.82  fof(f122,plain,(
% 3.69/0.82    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.69/0.82    inference(equality_resolution,[],[f106])).
% 3.69/0.82  fof(f106,plain,(
% 3.69/0.82    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.69/0.82    inference(cnf_transformation,[],[f68])).
% 3.69/0.82  fof(f68,plain,(
% 3.69/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.69/0.82    inference(flattening,[],[f67])).
% 3.69/0.82  fof(f67,plain,(
% 3.69/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.69/0.82    inference(nnf_transformation,[],[f3])).
% 3.69/0.82  fof(f3,axiom,(
% 3.69/0.82    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.69/0.82  fof(f3330,plain,(
% 3.69/0.82    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_34),
% 3.69/0.82    inference(backward_demodulation,[],[f141,f493])).
% 3.69/0.82  fof(f493,plain,(
% 3.69/0.82    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_34),
% 3.69/0.82    inference(avatar_component_clause,[],[f492])).
% 3.69/0.82  fof(f492,plain,(
% 3.69/0.82    spl4_34 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 3.69/0.82  fof(f141,plain,(
% 3.69/0.82    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.69/0.82    inference(forward_demodulation,[],[f78,f79])).
% 3.69/0.82  fof(f78,plain,(
% 3.69/0.82    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f4753,plain,(
% 3.69/0.82    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4752,f3559])).
% 3.69/0.82  fof(f3559,plain,(
% 3.69/0.82    v1_partfun1(sK2,k1_relat_1(sK2)) | ~spl4_34),
% 3.69/0.82    inference(subsumption_resolution,[],[f3558,f180])).
% 3.69/0.82  fof(f180,plain,(
% 3.69/0.82    v1_relat_1(sK2)),
% 3.69/0.82    inference(resolution,[],[f108,f75])).
% 3.69/0.82  fof(f75,plain,(
% 3.69/0.82    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f108,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.69/0.82    inference(cnf_transformation,[],[f47])).
% 3.69/0.82  fof(f47,plain,(
% 3.69/0.82    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.69/0.82    inference(ennf_transformation,[],[f8])).
% 3.69/0.82  fof(f8,axiom,(
% 3.69/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.69/0.82  fof(f3558,plain,(
% 3.69/0.82    v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_34),
% 3.69/0.82    inference(resolution,[],[f3431,f121])).
% 3.69/0.82  fof(f121,plain,(
% 3.69/0.82    ( ! [X1] : (~v4_relat_1(X1,k1_relat_1(X1)) | v1_partfun1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.69/0.82    inference(equality_resolution,[],[f103])).
% 3.69/0.82  fof(f103,plain,(
% 3.69/0.82    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.69/0.82    inference(cnf_transformation,[],[f66])).
% 3.69/0.82  fof(f66,plain,(
% 3.69/0.82    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.69/0.82    inference(nnf_transformation,[],[f45])).
% 3.69/0.82  fof(f45,plain,(
% 3.69/0.82    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.69/0.82    inference(flattening,[],[f44])).
% 3.69/0.82  fof(f44,plain,(
% 3.69/0.82    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.69/0.82    inference(ennf_transformation,[],[f14])).
% 3.69/0.82  fof(f14,axiom,(
% 3.69/0.82    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 3.69/0.82  fof(f3431,plain,(
% 3.69/0.82    ( ! [X0] : (v4_relat_1(sK2,X0)) ) | ~spl4_34),
% 3.69/0.82    inference(resolution,[],[f3361,f203])).
% 3.69/0.82  fof(f203,plain,(
% 3.69/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 3.69/0.82    inference(superposition,[],[f110,f122])).
% 3.69/0.82  fof(f110,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.69/0.82    inference(cnf_transformation,[],[f49])).
% 3.69/0.82  fof(f49,plain,(
% 3.69/0.82    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.69/0.82    inference(ennf_transformation,[],[f26])).
% 3.69/0.82  fof(f26,plain,(
% 3.69/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.69/0.82    inference(pure_predicate_removal,[],[f9])).
% 3.69/0.82  fof(f9,axiom,(
% 3.69/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.69/0.82  fof(f4752,plain,(
% 3.69/0.82    ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (spl4_1 | ~spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.82    inference(resolution,[],[f4726,f797])).
% 3.69/0.82  fof(f797,plain,(
% 3.69/0.82    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X0)) )),
% 3.69/0.82    inference(superposition,[],[f393,f122])).
% 3.69/0.82  fof(f393,plain,(
% 3.69/0.82    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | v1_funct_2(X0,k1_relat_1(X0),X1) | ~v1_funct_1(X0)) )),
% 3.69/0.82    inference(equality_resolution,[],[f281])).
% 3.69/0.82  fof(f281,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.69/0.82    inference(duplicate_literal_removal,[],[f280])).
% 3.69/0.82  fof(f280,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.69/0.82    inference(superposition,[],[f112,f109])).
% 3.69/0.82  fof(f109,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.69/0.82    inference(cnf_transformation,[],[f48])).
% 3.69/0.82  fof(f48,plain,(
% 3.69/0.82    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.69/0.82    inference(ennf_transformation,[],[f11])).
% 3.69/0.82  fof(f11,axiom,(
% 3.69/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.69/0.82  fof(f112,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.69/0.82    inference(cnf_transformation,[],[f51])).
% 3.69/0.82  fof(f51,plain,(
% 3.69/0.82    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.69/0.82    inference(flattening,[],[f50])).
% 3.69/0.82  fof(f50,plain,(
% 3.69/0.82    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.69/0.82    inference(ennf_transformation,[],[f15])).
% 3.69/0.82  fof(f15,axiom,(
% 3.69/0.82    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 3.69/0.82  fof(f4726,plain,(
% 3.69/0.82    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (spl4_1 | ~spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.82    inference(superposition,[],[f4724,f4465])).
% 3.69/0.82  fof(f4465,plain,(
% 3.69/0.82    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v1_partfun1(sK2,X0)) ) | (~spl4_31 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4464,f3431])).
% 3.69/0.82  fof(f4464,plain,(
% 3.69/0.82    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.82    inference(subsumption_resolution,[],[f4463,f180])).
% 3.69/0.82  fof(f4463,plain,(
% 3.69/0.82    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.82    inference(subsumption_resolution,[],[f4462,f199])).
% 3.69/0.82  fof(f199,plain,(
% 3.69/0.82    v4_relat_1(sK2,u1_struct_0(sK0))),
% 3.69/0.82    inference(resolution,[],[f110,f75])).
% 3.69/0.82  fof(f4462,plain,(
% 3.69/0.82    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.82    inference(resolution,[],[f478,f238])).
% 3.69/0.82  fof(f238,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X2) | X1 = X2 | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 3.69/0.82    inference(duplicate_literal_removal,[],[f235])).
% 3.69/0.82  fof(f235,plain,(
% 3.69/0.82    ( ! [X2,X0,X1] : (X1 = X2 | ~v1_partfun1(X0,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.69/0.82    inference(superposition,[],[f102,f102])).
% 3.69/0.82  fof(f102,plain,(
% 3.69/0.82    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.69/0.82    inference(cnf_transformation,[],[f66])).
% 3.69/0.82  fof(f478,plain,(
% 3.69/0.82    v1_partfun1(sK2,u1_struct_0(sK0)) | ~spl4_31),
% 3.69/0.82    inference(avatar_component_clause,[],[f477])).
% 3.69/0.82  fof(f477,plain,(
% 3.69/0.82    spl4_31 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 3.69/0.82  fof(f4724,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (spl4_1 | ~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4723,f69])).
% 3.69/0.82  fof(f69,plain,(
% 3.69/0.82    v2_pre_topc(sK0)),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f4723,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4722,f70])).
% 3.69/0.82  fof(f70,plain,(
% 3.69/0.82    l1_pre_topc(sK0)),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f4722,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4721,f74])).
% 3.69/0.82  fof(f74,plain,(
% 3.69/0.82    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f4721,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4720,f75])).
% 3.69/0.82  fof(f4720,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4719,f143])).
% 3.69/0.82  fof(f4719,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4718,f133])).
% 3.69/0.82  fof(f133,plain,(
% 3.69/0.82    ~v5_pre_topc(sK2,sK0,sK1) | spl4_1),
% 3.69/0.82    inference(avatar_component_clause,[],[f132])).
% 3.69/0.82  fof(f132,plain,(
% 3.69/0.82    spl4_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.69/0.82  fof(f4718,plain,(
% 3.69/0.82    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4716,f3361])).
% 3.69/0.82  fof(f4716,plain,(
% 3.69/0.82    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_22 | ~spl4_34)),
% 3.69/0.82    inference(resolution,[],[f3490,f313])).
% 3.69/0.82  fof(f313,plain,(
% 3.69/0.82    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_22),
% 3.69/0.82    inference(avatar_component_clause,[],[f312])).
% 3.69/0.82  fof(f312,plain,(
% 3.69/0.82    spl4_22 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 3.69/0.82  fof(f3490,plain,(
% 3.69/0.82    ( ! [X6,X7] : (~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_34),
% 3.69/0.82    inference(forward_demodulation,[],[f3489,f122])).
% 3.69/0.82  fof(f3489,plain,(
% 3.69/0.82    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_34),
% 3.69/0.82    inference(subsumption_resolution,[],[f3488,f71])).
% 3.69/0.82  fof(f71,plain,(
% 3.69/0.82    v2_pre_topc(sK1)),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f3488,plain,(
% 3.69/0.82    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_34),
% 3.69/0.82    inference(subsumption_resolution,[],[f3443,f72])).
% 3.69/0.82  fof(f72,plain,(
% 3.69/0.82    l1_pre_topc(sK1)),
% 3.69/0.82    inference(cnf_transformation,[],[f62])).
% 3.69/0.82  fof(f3443,plain,(
% 3.69/0.82    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v5_pre_topc(X6,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_34),
% 3.69/0.82    inference(superposition,[],[f130,f493])).
% 3.69/0.82  fof(f130,plain,(
% 3.69/0.82    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.82    inference(duplicate_literal_removal,[],[f117])).
% 3.69/0.82  fof(f117,plain,(
% 3.69/0.82    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.82    inference(equality_resolution,[],[f88])).
% 3.69/0.82  fof(f88,plain,(
% 3.69/0.82    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.82    inference(cnf_transformation,[],[f63])).
% 3.69/0.82  fof(f63,plain,(
% 3.69/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.69/0.82    inference(nnf_transformation,[],[f34])).
% 3.69/0.82  fof(f34,plain,(
% 3.69/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.69/0.82    inference(flattening,[],[f33])).
% 3.69/0.82  fof(f33,plain,(
% 3.69/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.69/0.82    inference(ennf_transformation,[],[f21])).
% 3.69/0.82  fof(f21,axiom,(
% 3.69/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.69/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 3.69/0.82  fof(f4438,plain,(
% 3.69/0.82    spl4_1 | ~spl4_22 | ~spl4_32 | ~spl4_34),
% 3.69/0.82    inference(avatar_contradiction_clause,[],[f4437])).
% 3.69/0.82  fof(f4437,plain,(
% 3.69/0.82    $false | (spl4_1 | ~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4436,f69])).
% 3.69/0.82  fof(f4436,plain,(
% 3.69/0.82    ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4435,f70])).
% 3.69/0.82  fof(f4435,plain,(
% 3.69/0.82    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4434,f143])).
% 3.69/0.82  fof(f4434,plain,(
% 3.69/0.82    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4433,f133])).
% 3.69/0.82  fof(f4433,plain,(
% 3.69/0.82    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4432,f3840])).
% 3.69/0.82  fof(f3840,plain,(
% 3.69/0.82    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl4_32),
% 3.69/0.82    inference(backward_demodulation,[],[f74,f481])).
% 3.69/0.82  fof(f481,plain,(
% 3.69/0.82    k1_xboole_0 = u1_struct_0(sK1) | ~spl4_32),
% 3.69/0.82    inference(avatar_component_clause,[],[f480])).
% 3.69/0.82  fof(f480,plain,(
% 3.69/0.82    spl4_32 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 3.69/0.82  fof(f4432,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4424,f3361])).
% 3.69/0.82  fof(f4424,plain,(
% 3.69/0.82    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_22 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(resolution,[],[f4353,f4132])).
% 3.69/0.82  fof(f4132,plain,(
% 3.69/0.82    v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_22 | ~spl4_32)),
% 3.69/0.82    inference(forward_demodulation,[],[f313,f481])).
% 3.69/0.82  fof(f4353,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X14,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_1(X14) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | (~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(duplicate_literal_removal,[],[f4352])).
% 3.69/0.82  fof(f4352,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~m1_subset_1(X14,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | (~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(forward_demodulation,[],[f4201,f3846])).
% 3.69/0.82  fof(f3846,plain,(
% 3.69/0.82    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(backward_demodulation,[],[f493,f481])).
% 3.69/0.82  fof(f4201,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | (~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(forward_demodulation,[],[f4200,f122])).
% 3.69/0.82  fof(f4200,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X14) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | (~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(duplicate_literal_removal,[],[f4199])).
% 3.69/0.82  fof(f4199,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | (~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(forward_demodulation,[],[f4198,f3846])).
% 3.69/0.82  fof(f4198,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | ~spl4_32),
% 3.69/0.82    inference(subsumption_resolution,[],[f4197,f71])).
% 3.69/0.82  fof(f4197,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | ~spl4_32),
% 3.69/0.82    inference(subsumption_resolution,[],[f4142,f72])).
% 3.69/0.82  fof(f4142,plain,(
% 3.69/0.82    ( ! [X14,X15] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X14,X15,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(X14,X15,sK1) | ~v1_funct_2(X14,u1_struct_0(X15),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X14) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k1_xboole_0))) | ~v1_funct_2(X14,u1_struct_0(X15),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15)) ) | ~spl4_32),
% 3.69/0.82    inference(superposition,[],[f130,f481])).
% 3.69/0.82  fof(f4131,plain,(
% 3.69/0.82    spl4_20 | ~spl4_32 | ~spl4_34),
% 3.69/0.82    inference(avatar_contradiction_clause,[],[f4130])).
% 3.69/0.82  fof(f4130,plain,(
% 3.69/0.82    $false | (spl4_20 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4129,f3840])).
% 3.69/0.82  fof(f4129,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (spl4_20 | ~spl4_32 | ~spl4_34)),
% 3.69/0.82    inference(forward_demodulation,[],[f4077,f3846])).
% 3.69/0.82  fof(f4077,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl4_20 | ~spl4_32)),
% 3.69/0.82    inference(forward_demodulation,[],[f307,f481])).
% 3.69/0.82  fof(f307,plain,(
% 3.69/0.82    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl4_20),
% 3.69/0.82    inference(avatar_component_clause,[],[f306])).
% 3.69/0.82  fof(f306,plain,(
% 3.69/0.82    spl4_20 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 3.69/0.82  fof(f4083,plain,(
% 3.69/0.82    ~spl4_32 | spl4_129 | ~spl4_137),
% 3.69/0.82    inference(avatar_contradiction_clause,[],[f4082])).
% 3.69/0.82  fof(f4082,plain,(
% 3.69/0.82    $false | (~spl4_32 | spl4_129 | ~spl4_137)),
% 3.69/0.82    inference(subsumption_resolution,[],[f4081,f2123])).
% 3.69/0.82  fof(f2123,plain,(
% 3.69/0.82    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl4_129),
% 3.69/0.82    inference(avatar_component_clause,[],[f2090])).
% 3.69/0.82  fof(f2090,plain,(
% 3.69/0.82    spl4_129 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 3.69/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).
% 3.69/0.83  fof(f4081,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_137)),
% 3.69/0.83    inference(forward_demodulation,[],[f2499,f481])).
% 3.69/0.83  fof(f2499,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_137),
% 3.69/0.83    inference(avatar_component_clause,[],[f2490])).
% 3.69/0.83  fof(f2490,plain,(
% 3.69/0.83    spl4_137 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).
% 3.69/0.83  fof(f4074,plain,(
% 3.69/0.83    ~spl4_1 | ~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f4073])).
% 3.69/0.83  fof(f4073,plain,(
% 3.69/0.83    $false | (~spl4_1 | ~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4072,f3840])).
% 3.69/0.83  fof(f4072,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl4_1 | ~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(forward_demodulation,[],[f4071,f481])).
% 3.69/0.83  fof(f4071,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_1 | ~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4070,f4064])).
% 3.69/0.83  fof(f4064,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(forward_demodulation,[],[f4063,f481])).
% 3.69/0.83  fof(f4063,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4062,f3361])).
% 3.69/0.83  fof(f4062,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_34 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4061,f3331])).
% 3.69/0.83  fof(f3331,plain,(
% 3.69/0.83    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_34),
% 3.69/0.83    inference(backward_demodulation,[],[f142,f493])).
% 3.69/0.83  fof(f142,plain,(
% 3.69/0.83    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.69/0.83    inference(forward_demodulation,[],[f77,f79])).
% 3.69/0.83  fof(f77,plain,(
% 3.69/0.83    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.69/0.83    inference(cnf_transformation,[],[f62])).
% 3.69/0.83  fof(f4061,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4060,f143])).
% 3.69/0.83  fof(f4060,plain,(
% 3.69/0.83    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_32 | ~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4059,f3840])).
% 3.69/0.83  fof(f4059,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4058,f70])).
% 3.69/0.83  fof(f4058,plain,(
% 3.69/0.83    ~l1_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_56 | spl4_137)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3798,f69])).
% 3.69/0.83  fof(f3798,plain,(
% 3.69/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_56 | spl4_137)),
% 3.69/0.83    inference(resolution,[],[f910,f2491])).
% 3.69/0.83  fof(f2491,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_137),
% 3.69/0.83    inference(avatar_component_clause,[],[f2490])).
% 3.69/0.83  fof(f910,plain,(
% 3.69/0.83    ( ! [X10,X11] : (v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0) | ~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl4_56),
% 3.69/0.83    inference(avatar_component_clause,[],[f909])).
% 3.69/0.83  fof(f909,plain,(
% 3.69/0.83    spl4_56 <=> ! [X11,X10] : (~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0) | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 3.69/0.83  fof(f4070,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_1 | ~spl4_32 | ~spl4_34)),
% 3.69/0.83    inference(forward_demodulation,[],[f4069,f481])).
% 3.69/0.83  fof(f4069,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_1 | ~spl4_32 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4068,f69])).
% 3.69/0.83  fof(f4068,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_32 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4067,f70])).
% 3.69/0.83  fof(f4067,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_32 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4066,f3361])).
% 3.69/0.83  fof(f4066,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_32 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f4065,f143])).
% 3.69/0.83  fof(f4065,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_32 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3784,f3840])).
% 3.69/0.83  fof(f3784,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3764,f138])).
% 3.69/0.83  fof(f138,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,sK1) | ~spl4_1),
% 3.69/0.83    inference(avatar_component_clause,[],[f132])).
% 3.69/0.83  fof(f3764,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_34),
% 3.69/0.83    inference(resolution,[],[f3487,f75])).
% 3.69/0.83  fof(f3487,plain,(
% 3.69/0.83    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v5_pre_topc(X4,X5,sK1) | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | ~spl4_34),
% 3.69/0.83    inference(forward_demodulation,[],[f3486,f122])).
% 3.69/0.83  fof(f3486,plain,(
% 3.69/0.83    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k1_xboole_0))) | ~v5_pre_topc(X4,X5,sK1) | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | ~spl4_34),
% 3.69/0.83    inference(subsumption_resolution,[],[f3485,f71])).
% 3.69/0.83  fof(f3485,plain,(
% 3.69/0.83    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k1_xboole_0))) | ~v5_pre_topc(X4,X5,sK1) | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | ~spl4_34),
% 3.69/0.83    inference(subsumption_resolution,[],[f3442,f72])).
% 3.69/0.83  fof(f3442,plain,(
% 3.69/0.83    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k1_xboole_0))) | ~v5_pre_topc(X4,X5,sK1) | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X4,u1_struct_0(X5),k1_xboole_0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | ~spl4_34),
% 3.69/0.83    inference(superposition,[],[f129,f493])).
% 3.69/0.83  fof(f129,plain,(
% 3.69/0.83    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f118])).
% 3.69/0.83  fof(f118,plain,(
% 3.69/0.83    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(equality_resolution,[],[f87])).
% 3.69/0.83  fof(f87,plain,(
% 3.69/0.83    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(cnf_transformation,[],[f63])).
% 3.69/0.83  fof(f3839,plain,(
% 3.69/0.83    spl4_31 | spl4_32),
% 3.69/0.83    inference(avatar_split_clause,[],[f3838,f480,f477])).
% 3.69/0.83  fof(f3838,plain,(
% 3.69/0.83    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0))),
% 3.69/0.83    inference(subsumption_resolution,[],[f3837,f143])).
% 3.69/0.83  fof(f3837,plain,(
% 3.69/0.83    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2299,f74])).
% 3.69/0.83  fof(f2299,plain,(
% 3.69/0.83    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 3.69/0.83    inference(resolution,[],[f75,f125])).
% 3.69/0.83  fof(f125,plain,(
% 3.69/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f114])).
% 3.69/0.83  fof(f114,plain,(
% 3.69/0.83    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.69/0.83    inference(cnf_transformation,[],[f53])).
% 3.69/0.83  fof(f53,plain,(
% 3.69/0.83    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.69/0.83    inference(flattening,[],[f52])).
% 3.69/0.83  fof(f52,plain,(
% 3.69/0.83    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.69/0.83    inference(ennf_transformation,[],[f16])).
% 3.69/0.83  fof(f16,axiom,(
% 3.69/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.69/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 3.69/0.83  fof(f3836,plain,(
% 3.69/0.83    ~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f3835])).
% 3.69/0.83  fof(f3835,plain,(
% 3.69/0.83    $false | (~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3834,f143])).
% 3.69/0.83  fof(f3834,plain,(
% 3.69/0.83    ~v1_funct_1(sK2) | (~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3833,f3361])).
% 3.69/0.83  fof(f3833,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3830,f3559])).
% 3.69/0.83  fof(f3830,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(resolution,[],[f3797,f797])).
% 3.69/0.83  fof(f3797,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3796,f3431])).
% 3.69/0.83  fof(f3796,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl4_1 | spl4_22 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(superposition,[],[f3790,f2326])).
% 3.69/0.83  fof(f2326,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.83    inference(subsumption_resolution,[],[f2325,f180])).
% 3.69/0.83  fof(f2325,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.83    inference(subsumption_resolution,[],[f2324,f199])).
% 3.69/0.83  fof(f2324,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.83    inference(resolution,[],[f478,f238])).
% 3.69/0.83  fof(f3790,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl4_1 | spl4_22 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3789,f69])).
% 3.69/0.83  fof(f3789,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl4_1 | spl4_22 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3788,f70])).
% 3.69/0.83  fof(f3788,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | spl4_22 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3787,f74])).
% 3.69/0.83  fof(f3787,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | spl4_22 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3786,f3361])).
% 3.69/0.83  fof(f3786,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | spl4_22 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3785,f143])).
% 3.69/0.83  fof(f3785,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | spl4_22 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3784,f2282])).
% 3.69/0.83  fof(f2282,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_22),
% 3.69/0.83    inference(avatar_component_clause,[],[f312])).
% 3.69/0.83  fof(f3753,plain,(
% 3.69/0.83    spl4_20 | ~spl4_31 | ~spl4_34),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f3752])).
% 3.69/0.83  fof(f3752,plain,(
% 3.69/0.83    $false | (spl4_20 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3751,f143])).
% 3.69/0.83  fof(f3751,plain,(
% 3.69/0.83    ~v1_funct_1(sK2) | (spl4_20 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3750,f3361])).
% 3.69/0.83  fof(f3750,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (spl4_20 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3747,f3559])).
% 3.69/0.83  fof(f3747,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (spl4_20 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(resolution,[],[f3737,f797])).
% 3.69/0.83  fof(f3737,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (spl4_20 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3736,f3431])).
% 3.69/0.83  fof(f3736,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_20 | ~spl4_31 | ~spl4_34)),
% 3.69/0.83    inference(superposition,[],[f3735,f2326])).
% 3.69/0.83  fof(f3735,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (spl4_20 | ~spl4_34)),
% 3.69/0.83    inference(forward_demodulation,[],[f307,f493])).
% 3.69/0.83  fof(f3316,plain,(
% 3.69/0.83    ~spl4_31 | ~spl4_162),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f3315])).
% 3.69/0.83  fof(f3315,plain,(
% 3.69/0.83    $false | (~spl4_31 | ~spl4_162)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3314,f74])).
% 3.69/0.83  fof(f3314,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_31 | ~spl4_162)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3309,f478])).
% 3.69/0.83  fof(f3309,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_162),
% 3.69/0.83    inference(resolution,[],[f3220,f75])).
% 3.69/0.83  fof(f3220,plain,(
% 3.69/0.83    ( ! [X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X3) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1))) ) | ~spl4_162),
% 3.69/0.83    inference(avatar_component_clause,[],[f3219])).
% 3.69/0.83  fof(f3219,plain,(
% 3.69/0.83    spl4_162 <=> ! [X3] : (~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~v1_partfun1(sK2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).
% 3.69/0.83  fof(f3221,plain,(
% 3.69/0.83    spl4_162 | spl4_27 | ~spl4_1 | ~spl4_31 | ~spl4_33),
% 3.69/0.83    inference(avatar_split_clause,[],[f3217,f489,f477,f132,f343,f3219])).
% 3.69/0.83  fof(f343,plain,(
% 3.69/0.83    spl4_27 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 3.69/0.83  fof(f489,plain,(
% 3.69/0.83    spl4_33 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 3.69/0.83  fof(f3217,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X3)) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3216,f110])).
% 3.69/0.83  fof(f3216,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3)) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3215,f199])).
% 3.69/0.83  fof(f3215,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3) | ~v4_relat_1(sK2,u1_struct_0(sK0))) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3214,f478])).
% 3.69/0.83  fof(f3214,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0))) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3213,f71])).
% 3.69/0.83  fof(f3213,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0))) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3212,f72])).
% 3.69/0.83  fof(f3212,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0))) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3211,f74])).
% 3.69/0.83  fof(f3211,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0))) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3139,f143])).
% 3.69/0.83  fof(f3139,plain,(
% 3.69/0.83    ( ! [X3] : (~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,X3,u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X3) | ~v4_relat_1(sK2,X3) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0))) ) | (~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f2576,f2381])).
% 3.69/0.83  fof(f2381,plain,(
% 3.69/0.83    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1)) ) | ~spl4_31),
% 3.69/0.83    inference(superposition,[],[f75,f2326])).
% 3.69/0.83  fof(f2576,plain,(
% 3.69/0.83    ( ! [X14,X12,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X14)))) | ~v5_pre_topc(X13,sK0,X14) | v5_pre_topc(X13,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X14) | ~v1_funct_2(X13,X12,u1_struct_0(X14)) | ~v1_funct_1(X13) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,u1_struct_0(X14)))) | ~v1_funct_2(X13,u1_struct_0(sK0),u1_struct_0(X14)) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | ~v1_partfun1(sK2,X12) | ~v4_relat_1(sK2,X12)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f2575,f69])).
% 3.69/0.83  fof(f2575,plain,(
% 3.69/0.83    ( ! [X14,X12,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,u1_struct_0(X14)))) | ~v5_pre_topc(X13,sK0,X14) | v5_pre_topc(X13,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X14) | ~v1_funct_2(X13,X12,u1_struct_0(X14)) | ~v1_funct_1(X13) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X14)))) | ~v1_funct_2(X13,u1_struct_0(sK0),u1_struct_0(X14)) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | ~v2_pre_topc(sK0) | ~v1_partfun1(sK2,X12) | ~v4_relat_1(sK2,X12)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f2543,f70])).
% 3.69/0.83  fof(f2543,plain,(
% 3.69/0.83    ( ! [X14,X12,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,u1_struct_0(X14)))) | ~v5_pre_topc(X13,sK0,X14) | v5_pre_topc(X13,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X14) | ~v1_funct_2(X13,X12,u1_struct_0(X14)) | ~v1_funct_1(X13) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X14)))) | ~v1_funct_2(X13,u1_struct_0(sK0),u1_struct_0(X14)) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_partfun1(sK2,X12) | ~v4_relat_1(sK2,X12)) ) | ~spl4_33),
% 3.69/0.83    inference(superposition,[],[f127,f1411])).
% 3.69/0.83  fof(f1411,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f1410,f180])).
% 3.69/0.83  fof(f1410,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f1409,f200])).
% 3.69/0.83  fof(f200,plain,(
% 3.69/0.83    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.69/0.83    inference(resolution,[],[f110,f141])).
% 3.69/0.83  fof(f1409,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_33),
% 3.69/0.83    inference(resolution,[],[f490,f238])).
% 3.69/0.83  fof(f490,plain,(
% 3.69/0.83    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl4_33),
% 3.69/0.83    inference(avatar_component_clause,[],[f489])).
% 3.69/0.83  fof(f127,plain,(
% 3.69/0.83    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f120])).
% 3.69/0.83  fof(f120,plain,(
% 3.69/0.83    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(equality_resolution,[],[f89])).
% 3.69/0.83  fof(f89,plain,(
% 3.69/0.83    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(cnf_transformation,[],[f64])).
% 3.69/0.83  fof(f64,plain,(
% 3.69/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.69/0.83    inference(nnf_transformation,[],[f36])).
% 3.69/0.83  fof(f36,plain,(
% 3.69/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.69/0.83    inference(flattening,[],[f35])).
% 3.69/0.83  fof(f35,plain,(
% 3.69/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.69/0.83    inference(ennf_transformation,[],[f20])).
% 3.69/0.83  fof(f20,axiom,(
% 3.69/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.69/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 3.69/0.83  fof(f3208,plain,(
% 3.69/0.83    spl4_1 | ~spl4_27 | ~spl4_31 | ~spl4_33),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f3207])).
% 3.69/0.83  fof(f3207,plain,(
% 3.69/0.83    $false | (spl4_1 | ~spl4_27 | ~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3206,f478])).
% 3.69/0.83  fof(f3206,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,u1_struct_0(sK0)) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3201,f74])).
% 3.69/0.83  fof(f3201,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_partfun1(sK2,u1_struct_0(sK0)) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f3167,f75])).
% 3.69/0.83  fof(f3167,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_partfun1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3166,f110])).
% 3.69/0.83  fof(f3166,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3165,f71])).
% 3.69/0.83  fof(f3165,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3164,f72])).
% 3.69/0.83  fof(f3164,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3163,f74])).
% 3.69/0.83  fof(f3163,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3162,f75])).
% 3.69/0.83  fof(f3162,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3161,f143])).
% 3.69/0.83  fof(f3161,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f3154,f133])).
% 3.69/0.83  fof(f3154,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl4_27 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f2578,f344])).
% 3.69/0.83  fof(f344,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl4_27),
% 3.69/0.83    inference(avatar_component_clause,[],[f343])).
% 3.69/0.83  fof(f2578,plain,(
% 3.69/0.83    ( ! [X17,X15,X16] : (~v5_pre_topc(X16,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X17) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,u1_struct_0(X17)))) | v5_pre_topc(X16,sK0,X17) | ~v1_funct_2(X16,X15,u1_struct_0(X17)) | ~v1_funct_1(X16) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~v1_partfun1(sK2,X15) | ~v4_relat_1(sK2,X15)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f2577,f69])).
% 3.69/0.83  fof(f2577,plain,(
% 3.69/0.83    ( ! [X17,X15,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,u1_struct_0(X17)))) | ~v5_pre_topc(X16,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X17) | v5_pre_topc(X16,sK0,X17) | ~v1_funct_2(X16,X15,u1_struct_0(X17)) | ~v1_funct_1(X16) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~v2_pre_topc(sK0) | ~v1_partfun1(sK2,X15) | ~v4_relat_1(sK2,X15)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f2544,f70])).
% 3.69/0.83  fof(f2544,plain,(
% 3.69/0.83    ( ! [X17,X15,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,u1_struct_0(X17)))) | ~v5_pre_topc(X16,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X17) | v5_pre_topc(X16,sK0,X17) | ~v1_funct_2(X16,X15,u1_struct_0(X17)) | ~v1_funct_1(X16) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X17)))) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_partfun1(sK2,X15) | ~v4_relat_1(sK2,X15)) ) | ~spl4_33),
% 3.69/0.83    inference(superposition,[],[f128,f1411])).
% 3.69/0.83  fof(f128,plain,(
% 3.69/0.83    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f119])).
% 3.69/0.83  fof(f119,plain,(
% 3.69/0.83    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(equality_resolution,[],[f90])).
% 3.69/0.83  fof(f90,plain,(
% 3.69/0.83    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(cnf_transformation,[],[f64])).
% 3.69/0.83  fof(f2484,plain,(
% 3.69/0.83    spl4_25 | ~spl4_31 | ~spl4_33),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f2483])).
% 3.69/0.83  fof(f2483,plain,(
% 3.69/0.83    $false | (spl4_25 | ~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2482,f200])).
% 3.69/0.83  fof(f2482,plain,(
% 3.69/0.83    ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (spl4_25 | ~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2480,f490])).
% 3.69/0.83  fof(f2480,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (spl4_25 | ~spl4_31)),
% 3.69/0.83    inference(resolution,[],[f2380,f338])).
% 3.69/0.83  fof(f338,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl4_25),
% 3.69/0.83    inference(avatar_component_clause,[],[f337])).
% 3.69/0.83  fof(f337,plain,(
% 3.69/0.83    spl4_25 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 3.69/0.83  fof(f2380,plain,(
% 3.69/0.83    ( ! [X0] : (v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_31),
% 3.69/0.83    inference(superposition,[],[f74,f2326])).
% 3.69/0.83  fof(f2298,plain,(
% 3.69/0.83    spl4_74),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f2297])).
% 3.69/0.83  fof(f2297,plain,(
% 3.69/0.83    $false | spl4_74),
% 3.69/0.83    inference(subsumption_resolution,[],[f1260,f142])).
% 3.69/0.83  fof(f1260,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl4_74),
% 3.69/0.83    inference(avatar_component_clause,[],[f1259])).
% 3.69/0.83  fof(f1259,plain,(
% 3.69/0.83    spl4_74 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 3.69/0.83  fof(f2296,plain,(
% 3.69/0.83    ~spl4_23 | ~spl4_24 | ~spl4_25 | ~spl4_26 | ~spl4_74 | spl4_2 | ~spl4_27),
% 3.69/0.83    inference(avatar_split_clause,[],[f2295,f343,f135,f1259,f340,f337,f334,f331])).
% 3.69/0.83  fof(f331,plain,(
% 3.69/0.83    spl4_23 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 3.69/0.83  fof(f334,plain,(
% 3.69/0.83    spl4_24 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.69/0.83  fof(f340,plain,(
% 3.69/0.83    spl4_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 3.69/0.83  fof(f135,plain,(
% 3.69/0.83    spl4_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.69/0.83  fof(f2295,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl4_2 | ~spl4_27)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2294,f2280])).
% 3.69/0.83  fof(f2280,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_2),
% 3.69/0.83    inference(forward_demodulation,[],[f136,f79])).
% 3.69/0.83  fof(f136,plain,(
% 3.69/0.83    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_2),
% 3.69/0.83    inference(avatar_component_clause,[],[f135])).
% 3.69/0.83  fof(f2294,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_27),
% 3.69/0.83    inference(subsumption_resolution,[],[f2141,f344])).
% 3.69/0.83  fof(f2141,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    inference(subsumption_resolution,[],[f2140,f71])).
% 3.69/0.83  fof(f2140,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    inference(subsumption_resolution,[],[f2139,f72])).
% 3.69/0.83  fof(f2139,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    inference(subsumption_resolution,[],[f977,f143])).
% 3.69/0.83  fof(f977,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    inference(resolution,[],[f141,f129])).
% 3.69/0.83  fof(f2293,plain,(
% 3.69/0.83    ~spl4_18 | ~spl4_19 | ~spl4_20 | ~spl4_21 | ~spl4_74 | ~spl4_22 | spl4_2),
% 3.69/0.83    inference(avatar_split_clause,[],[f2292,f135,f312,f1259,f309,f306,f303,f300])).
% 3.69/0.83  fof(f300,plain,(
% 3.69/0.83    spl4_18 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.69/0.83  fof(f303,plain,(
% 3.69/0.83    spl4_19 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.69/0.83  fof(f309,plain,(
% 3.69/0.83    spl4_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.69/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.69/0.83  fof(f2292,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f2153,f2280])).
% 3.69/0.83  fof(f2153,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.69/0.83    inference(subsumption_resolution,[],[f2152,f69])).
% 3.69/0.83  fof(f2152,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2151,f70])).
% 3.69/0.83  fof(f2151,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.69/0.83    inference(subsumption_resolution,[],[f975,f143])).
% 3.69/0.83  fof(f975,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.69/0.83    inference(resolution,[],[f141,f127])).
% 3.69/0.83  fof(f2279,plain,(
% 3.69/0.83    spl4_2 | ~spl4_32 | ~spl4_129),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f2278])).
% 3.69/0.83  fof(f2278,plain,(
% 3.69/0.83    $false | (spl4_2 | ~spl4_32 | ~spl4_129)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2091,f2245])).
% 3.69/0.83  fof(f2245,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl4_2 | ~spl4_32)),
% 3.69/0.83    inference(forward_demodulation,[],[f2244,f79])).
% 3.69/0.83  fof(f2244,plain,(
% 3.69/0.83    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl4_2 | ~spl4_32)),
% 3.69/0.83    inference(forward_demodulation,[],[f136,f481])).
% 3.69/0.83  fof(f2091,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl4_129),
% 3.69/0.83    inference(avatar_component_clause,[],[f2090])).
% 3.69/0.83  fof(f2277,plain,(
% 3.69/0.83    ~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f2274])).
% 3.69/0.83  fof(f2274,plain,(
% 3.69/0.83    $false | (~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f2271,f1335])).
% 3.69/0.83  fof(f1335,plain,(
% 3.69/0.83    v1_partfun1(sK2,k1_relat_1(sK2)) | ~spl4_32),
% 3.69/0.83    inference(subsumption_resolution,[],[f1334,f180])).
% 3.69/0.83  fof(f1334,plain,(
% 3.69/0.83    v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_32),
% 3.69/0.83    inference(resolution,[],[f1327,f121])).
% 3.69/0.83  fof(f1327,plain,(
% 3.69/0.83    ( ! [X0] : (v4_relat_1(sK2,X0)) ) | ~spl4_32),
% 3.69/0.83    inference(resolution,[],[f1303,f203])).
% 3.69/0.83  fof(f1303,plain,(
% 3.69/0.83    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_32),
% 3.69/0.83    inference(forward_demodulation,[],[f1278,f122])).
% 3.69/0.83  fof(f1278,plain,(
% 3.69/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl4_32),
% 3.69/0.83    inference(backward_demodulation,[],[f75,f481])).
% 3.69/0.83  fof(f2271,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_partfun1(sK2,X0)) ) | (~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2270,f2042])).
% 3.69/0.83  fof(f2042,plain,(
% 3.69/0.83    ( ! [X0] : (v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2038,f1303])).
% 3.69/0.83  fof(f2038,plain,(
% 3.69/0.83    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(superposition,[],[f2034,f122])).
% 3.69/0.83  fof(f2034,plain,(
% 3.69/0.83    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK2,X0,X1) | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(equality_resolution,[],[f1809])).
% 3.69/0.83  fof(f1809,plain,(
% 3.69/0.83    ( ! [X6,X7,X5] : (X5 != X6 | v1_funct_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_partfun1(sK2,X5)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1806,f143])).
% 3.69/0.83  fof(f1806,plain,(
% 3.69/0.83    ( ! [X6,X7,X5] : (X5 != X6 | v1_funct_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK2) | ~v1_partfun1(sK2,X5)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(superposition,[],[f281,f1783])).
% 3.69/0.83  fof(f1783,plain,(
% 3.69/0.83    ( ! [X0] : (k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f1557,f1335])).
% 3.69/0.83  fof(f1557,plain,(
% 3.69/0.83    ( ! [X0,X1] : (~v1_partfun1(sK2,X1) | X0 = X1 | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(superposition,[],[f1412,f1412])).
% 3.69/0.83  fof(f1412,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1411,f1327])).
% 3.69/0.83  fof(f2270,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2269,f1277])).
% 3.69/0.83  fof(f1277,plain,(
% 3.69/0.83    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl4_32),
% 3.69/0.83    inference(backward_demodulation,[],[f74,f481])).
% 3.69/0.83  fof(f2269,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2268,f143])).
% 3.69/0.83  fof(f2268,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2267,f1303])).
% 3.69/0.83  fof(f2267,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_funct_2(sK2,X0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_1 | spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2264,f138])).
% 3.69/0.83  fof(f2264,plain,(
% 3.69/0.83    ( ! [X0] : (~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,X0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f1718,f2149])).
% 3.69/0.83  fof(f2149,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl4_27),
% 3.69/0.83    inference(avatar_component_clause,[],[f343])).
% 3.69/0.83  fof(f1718,plain,(
% 3.69/0.83    ( ! [X0,X1] : (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(X1,sK0,sK1) | ~v1_funct_2(X1,X0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),k1_xboole_0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1717,f69])).
% 3.69/0.83  fof(f1717,plain,(
% 3.69/0.83    ( ! [X0,X1] : (~v1_funct_2(X1,X0,k1_xboole_0) | ~v5_pre_topc(X1,sK0,sK1) | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1710,f70])).
% 3.69/0.83  fof(f1710,plain,(
% 3.69/0.83    ( ! [X0,X1] : (~v1_funct_2(X1,X0,k1_xboole_0) | ~v5_pre_topc(X1,sK0,sK1) | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_partfun1(sK2,X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(superposition,[],[f1362,f1412])).
% 3.69/0.83  fof(f1362,plain,(
% 3.69/0.83    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_32),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f1361])).
% 3.69/0.83  fof(f1361,plain,(
% 3.69/0.83    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_32),
% 3.69/0.83    inference(forward_demodulation,[],[f1360,f122])).
% 3.69/0.83  fof(f1360,plain,(
% 3.69/0.83    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_32),
% 3.69/0.83    inference(forward_demodulation,[],[f1359,f122])).
% 3.69/0.83  fof(f1359,plain,(
% 3.69/0.83    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0))) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_32),
% 3.69/0.83    inference(subsumption_resolution,[],[f1358,f71])).
% 3.69/0.83  fof(f1358,plain,(
% 3.69/0.83    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0))) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_32),
% 3.69/0.83    inference(subsumption_resolution,[],[f1339,f72])).
% 3.69/0.83  fof(f1339,plain,(
% 3.69/0.83    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0))) | ~v5_pre_topc(X2,X3,sK1) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_32),
% 3.69/0.83    inference(superposition,[],[f127,f481])).
% 3.69/0.83  fof(f2078,plain,(
% 3.69/0.83    spl4_1 | ~spl4_27 | ~spl4_32 | ~spl4_33),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f2077])).
% 3.69/0.83  fof(f2077,plain,(
% 3.69/0.83    $false | (spl4_1 | ~spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2076,f69])).
% 3.69/0.83  fof(f2076,plain,(
% 3.69/0.83    ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2075,f70])).
% 3.69/0.83  fof(f2075,plain,(
% 3.69/0.83    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2074,f1277])).
% 3.69/0.83  fof(f2074,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2073,f133])).
% 3.69/0.83  fof(f2073,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2070,f490])).
% 3.69/0.83  fof(f2070,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_27 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f2058,f344])).
% 3.69/0.83  fof(f2058,plain,(
% 3.69/0.83    ( ! [X0] : (~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(sK2,X0,sK1) | ~v1_funct_2(sK2,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2057,f143])).
% 3.69/0.83  fof(f2057,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | v5_pre_topc(sK2,X0,sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2055,f1303])).
% 3.69/0.83  fof(f2055,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | v5_pre_topc(sK2,X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f2042,f1370])).
% 3.69/0.83  fof(f1370,plain,(
% 3.69/0.83    ( ! [X6,X7] : (~v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0) | ~v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1) | v5_pre_topc(X6,X7,sK1) | ~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_32),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f1369])).
% 3.69/0.83  fof(f1369,plain,(
% 3.69/0.83    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_32),
% 3.69/0.83    inference(forward_demodulation,[],[f1368,f122])).
% 3.69/0.83  fof(f1368,plain,(
% 3.69/0.83    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_32),
% 3.69/0.83    inference(forward_demodulation,[],[f1367,f122])).
% 3.69/0.83  fof(f1367,plain,(
% 3.69/0.83    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0))) | ~v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_32),
% 3.69/0.83    inference(subsumption_resolution,[],[f1366,f71])).
% 3.69/0.83  fof(f1366,plain,(
% 3.69/0.83    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0))) | ~v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_32),
% 3.69/0.83    inference(subsumption_resolution,[],[f1341,f72])).
% 3.69/0.83  fof(f1341,plain,(
% 3.69/0.83    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0))) | ~v5_pre_topc(X6,g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)),sK1) | v5_pre_topc(X6,X7,sK1) | ~v1_funct_2(X6,u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),k1_xboole_0) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),k1_xboole_0))) | ~v1_funct_2(X6,u1_struct_0(X7),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | ~spl4_32),
% 3.69/0.83    inference(superposition,[],[f128,f481])).
% 3.69/0.83  fof(f2053,plain,(
% 3.69/0.83    spl4_25 | ~spl4_32 | ~spl4_33),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f2050])).
% 3.69/0.83  fof(f2050,plain,(
% 3.69/0.83    $false | (spl4_25 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f2043,f1335])).
% 3.69/0.83  fof(f2043,plain,(
% 3.69/0.83    ( ! [X0] : (~v1_partfun1(sK2,X0)) ) | (spl4_25 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f2042,f1563])).
% 3.69/0.83  fof(f1563,plain,(
% 3.69/0.83    ( ! [X6] : (~v1_funct_2(sK2,X6,k1_xboole_0) | ~v1_partfun1(sK2,X6)) ) | (spl4_25 | ~spl4_32 | ~spl4_33)),
% 3.69/0.83    inference(superposition,[],[f1323,f1412])).
% 3.69/0.83  fof(f1323,plain,(
% 3.69/0.83    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl4_25 | ~spl4_32)),
% 3.69/0.83    inference(forward_demodulation,[],[f338,f481])).
% 3.69/0.83  fof(f1266,plain,(
% 3.69/0.83    ~spl4_23 | ~spl4_24 | ~spl4_25 | ~spl4_26 | ~spl4_74 | spl4_27 | ~spl4_2),
% 3.69/0.83    inference(avatar_split_clause,[],[f1265,f135,f343,f1259,f340,f337,f334,f331])).
% 3.69/0.83  fof(f1265,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f1264,f71])).
% 3.69/0.83  fof(f1264,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f1263,f72])).
% 3.69/0.83  fof(f1263,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f1262,f143])).
% 3.69/0.83  fof(f1262,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f705,f145])).
% 3.69/0.83  fof(f145,plain,(
% 3.69/0.83    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_2),
% 3.69/0.83    inference(forward_demodulation,[],[f139,f79])).
% 3.69/0.83  fof(f139,plain,(
% 3.69/0.83    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_2),
% 3.69/0.83    inference(avatar_component_clause,[],[f135])).
% 3.69/0.83  fof(f705,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.69/0.83    inference(resolution,[],[f141,f130])).
% 3.69/0.83  fof(f1098,plain,(
% 3.69/0.83    spl4_33 | spl4_34),
% 3.69/0.83    inference(avatar_split_clause,[],[f1097,f492,f489])).
% 3.69/0.83  fof(f1097,plain,(
% 3.69/0.83    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.69/0.83    inference(subsumption_resolution,[],[f1096,f143])).
% 3.69/0.83  fof(f1096,plain,(
% 3.69/0.83    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(sK2)),
% 3.69/0.83    inference(subsumption_resolution,[],[f978,f142])).
% 3.69/0.83  fof(f978,plain,(
% 3.69/0.83    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2)),
% 3.69/0.83    inference(resolution,[],[f141,f125])).
% 3.69/0.83  fof(f1077,plain,(
% 3.69/0.83    spl4_26 | ~spl4_32),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f1076])).
% 3.69/0.83  fof(f1076,plain,(
% 3.69/0.83    $false | (spl4_26 | ~spl4_32)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1075,f1069])).
% 3.69/0.83  fof(f1069,plain,(
% 3.69/0.83    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_32),
% 3.69/0.83    inference(forward_demodulation,[],[f1047,f122])).
% 3.69/0.83  fof(f1047,plain,(
% 3.69/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl4_32),
% 3.69/0.83    inference(backward_demodulation,[],[f75,f481])).
% 3.69/0.83  fof(f1075,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl4_26 | ~spl4_32)),
% 3.69/0.83    inference(forward_demodulation,[],[f1058,f122])).
% 3.69/0.83  fof(f1058,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (spl4_26 | ~spl4_32)),
% 3.69/0.83    inference(backward_demodulation,[],[f341,f481])).
% 3.69/0.83  fof(f341,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl4_26),
% 3.69/0.83    inference(avatar_component_clause,[],[f340])).
% 3.69/0.83  fof(f1045,plain,(
% 3.69/0.83    spl4_26 | ~spl4_31 | ~spl4_33),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f1044])).
% 3.69/0.83  fof(f1044,plain,(
% 3.69/0.83    $false | (spl4_26 | ~spl4_31 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1041,f478])).
% 3.69/0.83  fof(f1041,plain,(
% 3.69/0.83    ~v1_partfun1(sK2,u1_struct_0(sK0)) | (spl4_26 | ~spl4_33)),
% 3.69/0.83    inference(resolution,[],[f1031,f75])).
% 3.69/0.83  fof(f1031,plain,(
% 3.69/0.83    ( ! [X6] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X6)) ) | (spl4_26 | ~spl4_33)),
% 3.69/0.83    inference(subsumption_resolution,[],[f1008,f110])).
% 3.69/0.83  fof(f1008,plain,(
% 3.69/0.83    ( ! [X6] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X6) | ~v4_relat_1(sK2,X6)) ) | (spl4_26 | ~spl4_33)),
% 3.69/0.83    inference(superposition,[],[f341,f992])).
% 3.69/0.83  fof(f992,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f991,f180])).
% 3.69/0.83  fof(f991,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_33),
% 3.69/0.83    inference(subsumption_resolution,[],[f989,f200])).
% 3.69/0.83  fof(f989,plain,(
% 3.69/0.83    ( ! [X0] : (u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(sK2) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | ~spl4_33),
% 3.69/0.83    inference(resolution,[],[f490,f238])).
% 3.69/0.83  fof(f911,plain,(
% 3.69/0.83    ~spl4_18 | ~spl4_19 | spl4_56 | ~spl4_34),
% 3.69/0.83    inference(avatar_split_clause,[],[f907,f492,f909,f303,f300])).
% 3.69/0.83  fof(f907,plain,(
% 3.69/0.83    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11)) ) | ~spl4_34),
% 3.69/0.83    inference(duplicate_literal_removal,[],[f906])).
% 3.69/0.83  fof(f906,plain,(
% 3.69/0.83    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0) | ~v1_funct_1(X10) | ~v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11)) ) | ~spl4_34),
% 3.69/0.83    inference(forward_demodulation,[],[f905,f122])).
% 3.69/0.83  fof(f905,plain,(
% 3.69/0.83    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0) | ~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k1_xboole_0))) | ~v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11)) ) | ~spl4_34),
% 3.69/0.83    inference(forward_demodulation,[],[f867,f122])).
% 3.69/0.83  fof(f867,plain,(
% 3.69/0.83    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0))) | ~v5_pre_topc(X10,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X10,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(X10,u1_struct_0(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))),k1_xboole_0) | ~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k1_xboole_0))) | ~v1_funct_2(X10,u1_struct_0(X11),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11)) ) | ~spl4_34),
% 3.69/0.83    inference(superposition,[],[f127,f493])).
% 3.69/0.83  fof(f787,plain,(
% 3.69/0.83    ~spl4_18 | ~spl4_19 | ~spl4_20 | ~spl4_21 | spl4_22 | ~spl4_2),
% 3.69/0.83    inference(avatar_split_clause,[],[f786,f135,f312,f309,f306,f303,f300])).
% 3.69/0.83  fof(f786,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f785,f69])).
% 3.69/0.83  fof(f785,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f784,f70])).
% 3.69/0.83  fof(f784,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f783,f143])).
% 3.69/0.83  fof(f783,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f782,f142])).
% 3.69/0.83  fof(f782,plain,(
% 3.69/0.83    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_2),
% 3.69/0.83    inference(subsumption_resolution,[],[f703,f145])).
% 3.69/0.83  fof(f703,plain,(
% 3.69/0.83    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.69/0.83    inference(resolution,[],[f141,f128])).
% 3.69/0.83  fof(f694,plain,(
% 3.69/0.83    spl4_21 | ~spl4_34),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f693])).
% 3.69/0.83  fof(f693,plain,(
% 3.69/0.83    $false | (spl4_21 | ~spl4_34)),
% 3.69/0.83    inference(subsumption_resolution,[],[f692,f686])).
% 3.69/0.83  fof(f686,plain,(
% 3.69/0.83    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_34),
% 3.69/0.83    inference(forward_demodulation,[],[f671,f122])).
% 3.69/0.83  fof(f671,plain,(
% 3.69/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_34),
% 3.69/0.83    inference(backward_demodulation,[],[f141,f493])).
% 3.69/0.83  fof(f692,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl4_21 | ~spl4_34)),
% 3.69/0.83    inference(forward_demodulation,[],[f677,f122])).
% 3.69/0.83  fof(f677,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (spl4_21 | ~spl4_34)),
% 3.69/0.83    inference(backward_demodulation,[],[f310,f493])).
% 3.69/0.83  fof(f310,plain,(
% 3.69/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl4_21),
% 3.69/0.83    inference(avatar_component_clause,[],[f309])).
% 3.69/0.83  fof(f378,plain,(
% 3.69/0.83    spl4_24),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f377])).
% 3.69/0.83  fof(f377,plain,(
% 3.69/0.83    $false | spl4_24),
% 3.69/0.83    inference(subsumption_resolution,[],[f374,f70])).
% 3.69/0.83  fof(f374,plain,(
% 3.69/0.83    ~l1_pre_topc(sK0) | spl4_24),
% 3.69/0.83    inference(resolution,[],[f197,f335])).
% 3.69/0.83  fof(f335,plain,(
% 3.69/0.83    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl4_24),
% 3.69/0.83    inference(avatar_component_clause,[],[f334])).
% 3.69/0.83  fof(f197,plain,(
% 3.69/0.83    ( ! [X1] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1)) )),
% 3.69/0.83    inference(resolution,[],[f98,f84])).
% 3.69/0.83  fof(f84,plain,(
% 3.69/0.83    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.69/0.83    inference(cnf_transformation,[],[f29])).
% 3.69/0.83  fof(f29,plain,(
% 3.69/0.83    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.83    inference(ennf_transformation,[],[f18])).
% 3.69/0.83  fof(f18,axiom,(
% 3.69/0.83    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 3.69/0.83  fof(f98,plain,(
% 3.69/0.83    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 3.69/0.83    inference(cnf_transformation,[],[f41])).
% 3.69/0.83  fof(f41,plain,(
% 3.69/0.83    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.69/0.83    inference(ennf_transformation,[],[f25])).
% 3.69/0.83  fof(f25,plain,(
% 3.69/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.69/0.83    inference(pure_predicate_removal,[],[f17])).
% 3.69/0.83  fof(f17,axiom,(
% 3.69/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.69/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.69/0.83  fof(f376,plain,(
% 3.69/0.83    spl4_19),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f375])).
% 3.69/0.83  fof(f375,plain,(
% 3.69/0.83    $false | spl4_19),
% 3.69/0.83    inference(subsumption_resolution,[],[f373,f72])).
% 3.69/0.83  fof(f373,plain,(
% 3.69/0.83    ~l1_pre_topc(sK1) | spl4_19),
% 3.69/0.83    inference(resolution,[],[f197,f304])).
% 3.69/0.83  fof(f304,plain,(
% 3.69/0.83    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_19),
% 3.69/0.83    inference(avatar_component_clause,[],[f303])).
% 3.69/0.83  fof(f349,plain,(
% 3.69/0.83    spl4_23),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f348])).
% 3.69/0.83  fof(f348,plain,(
% 3.69/0.83    $false | spl4_23),
% 3.69/0.83    inference(subsumption_resolution,[],[f347,f69])).
% 3.69/0.83  fof(f347,plain,(
% 3.69/0.83    ~v2_pre_topc(sK0) | spl4_23),
% 3.69/0.83    inference(subsumption_resolution,[],[f346,f70])).
% 3.69/0.83  fof(f346,plain,(
% 3.69/0.83    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl4_23),
% 3.69/0.83    inference(resolution,[],[f332,f86])).
% 3.69/0.83  fof(f86,plain,(
% 3.69/0.83    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.69/0.83    inference(cnf_transformation,[],[f32])).
% 3.69/0.83  fof(f32,plain,(
% 3.69/0.83    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.69/0.83    inference(flattening,[],[f31])).
% 3.69/0.83  fof(f31,plain,(
% 3.69/0.83    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.69/0.83    inference(ennf_transformation,[],[f24])).
% 3.69/0.83  fof(f24,plain,(
% 3.69/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.69/0.83    inference(pure_predicate_removal,[],[f19])).
% 3.69/0.83  fof(f19,axiom,(
% 3.69/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.69/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 3.69/0.83  fof(f332,plain,(
% 3.69/0.83    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl4_23),
% 3.69/0.83    inference(avatar_component_clause,[],[f331])).
% 3.69/0.83  fof(f321,plain,(
% 3.69/0.83    spl4_18),
% 3.69/0.83    inference(avatar_contradiction_clause,[],[f320])).
% 3.69/0.83  fof(f320,plain,(
% 3.69/0.83    $false | spl4_18),
% 3.69/0.83    inference(subsumption_resolution,[],[f319,f71])).
% 3.69/0.83  fof(f319,plain,(
% 3.69/0.83    ~v2_pre_topc(sK1) | spl4_18),
% 3.69/0.83    inference(subsumption_resolution,[],[f318,f72])).
% 3.69/0.83  fof(f318,plain,(
% 3.69/0.83    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl4_18),
% 3.69/0.83    inference(resolution,[],[f301,f86])).
% 3.69/0.83  fof(f301,plain,(
% 3.69/0.83    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_18),
% 3.69/0.83    inference(avatar_component_clause,[],[f300])).
% 3.69/0.83  fof(f140,plain,(
% 3.69/0.83    spl4_1 | spl4_2),
% 3.69/0.83    inference(avatar_split_clause,[],[f80,f135,f132])).
% 3.69/0.83  fof(f80,plain,(
% 3.69/0.83    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.69/0.83    inference(cnf_transformation,[],[f62])).
% 3.69/0.83  fof(f137,plain,(
% 3.69/0.83    ~spl4_1 | ~spl4_2),
% 3.69/0.83    inference(avatar_split_clause,[],[f81,f135,f132])).
% 3.69/0.83  fof(f81,plain,(
% 3.69/0.83    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.69/0.83    inference(cnf_transformation,[],[f62])).
% 3.69/0.83  % SZS output end Proof for theBenchmark
% 3.69/0.83  % (31399)------------------------------
% 3.69/0.83  % (31399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.83  % (31399)Termination reason: Refutation
% 3.69/0.83  
% 3.69/0.83  % (31399)Memory used [KB]: 13432
% 3.69/0.83  % (31399)Time elapsed: 0.427 s
% 3.69/0.83  % (31399)------------------------------
% 3.69/0.83  % (31399)------------------------------
% 3.69/0.83  % (31396)Success in time 0.481 s
%------------------------------------------------------------------------------
