%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:15 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  270 (24205 expanded)
%              Number of leaves         :   16 (12430 expanded)
%              Depth                    :   55
%              Number of atoms          : 1965 (612703 expanded)
%              Number of equality atoms :   78 (1924 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(subsumption_resolution,[],[f395,f233])).

fof(f233,plain,(
    ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f221,f232])).

fof(f232,plain,(
    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f231,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

% (8588)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (8593)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f37,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
    & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f36,f35,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                              | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                              | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                            & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X2)
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1)
                          | ~ v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5)) )
                        & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1)
                        & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                      & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1)
                      & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                    & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1)
                    & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                  & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1)
                  & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,sK2)
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                  | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                  | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1)
                & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,sK2)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1)
                | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5)) )
              & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
              & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,sK2)
          & m1_pre_topc(sK2,sK3)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1)
              | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
              | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5)) )
            & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
            & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X4,sK2)
        & m1_pre_topc(sK2,sK3)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1)
            | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1))
            | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5)) )
          & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
          & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK4,sK2)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1)
          | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1))
          | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5)) )
        & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
        & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
      & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
      & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X2)
                            & m1_pre_topc(X2,X3) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                               => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X2)
                          & m1_pre_topc(X2,X3) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                             => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_tmap_1)).

fof(f231,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f230,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f229,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f228,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f227,f43])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f227,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f44])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f226,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f48])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f225,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f50])).

fof(f50,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f224,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f53])).

fof(f53,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f223,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f54])).

fof(f54,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f222,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f203,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f203,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f74,f190])).

fof(f190,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
    inference(forward_demodulation,[],[f176,f152])).

fof(f152,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f142,f120])).

fof(f120,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(resolution,[],[f119,f52])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f111,f51])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X6,X7)
      | m1_pre_topc(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f106,f93])).

fof(f93,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f90,f48])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f88,f41])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f40])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f106,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X7,sK3)
      | m1_pre_topc(X6,sK3)
      | ~ v2_pre_topc(sK3) ) ),
    inference(resolution,[],[f70,f81])).

fof(f81,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f78,f48])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f61,f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f141,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f140,f93])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f139,f81])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f136,f44])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f135,f53])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f133,f54])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f176,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f174,f120])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f173,f39])).

fof(f173,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f40])).

fof(f172,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f41])).

fof(f171,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f170,f48])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f169,f42])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f168,f43])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f167,f44])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f166,f54])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f163,f55])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X2))
      | k3_tmap_1(X3,X2,X1,X0,sK5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f160,f70])).

fof(f160,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X2))
      | k3_tmap_1(X3,X2,X1,X0,sK5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X3)
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f221,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f209,f220])).

fof(f220,plain,(
    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f219,f39])).

fof(f219,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f218,f40])).

fof(f218,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f217,f41])).

fof(f217,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f42])).

fof(f216,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f43])).

fof(f215,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f214,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f213,f48])).

fof(f213,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f212,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f53])).

fof(f211,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f54])).

fof(f210,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f55])).

fof(f202,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f75,f190])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f209,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f194,f208])).

fof(f208,plain,(
    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f207,f39])).

fof(f207,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f40])).

fof(f206,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f41])).

fof(f205,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f48])).

fof(f204,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f50])).

fof(f201,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f131,f190])).

fof(f131,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f130,f42])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f129,f43])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f125,f55])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK5))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X0,X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f73,f53])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f194,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) ),
    inference(forward_demodulation,[],[f193,f190])).

fof(f193,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f192,f190])).

fof(f192,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f191,f190])).

fof(f191,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f60,f190])).

fof(f60,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f395,plain,(
    v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) ),
    inference(backward_demodulation,[],[f310,f390])).

fof(f390,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) ),
    inference(subsumption_resolution,[],[f389,f315])).

fof(f315,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f314,f39])).

fof(f314,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f40])).

fof(f313,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f41])).

fof(f312,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f46])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f311,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f303,f50])).

fof(f303,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f251,f298])).

fof(f298,plain,(
    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f297,f39])).

fof(f297,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f296,f40])).

fof(f296,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f294,f41])).

fof(f294,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f293,f46])).

fof(f293,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f292,f184])).

fof(f184,plain,(
    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4)) ),
    inference(backward_demodulation,[],[f153,f177])).

fof(f177,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2) ),
    inference(forward_demodulation,[],[f175,f151])).

fof(f151,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f142,f51])).

fof(f175,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f174,f51])).

fof(f153,plain,(
    k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) ),
    inference(resolution,[],[f150,f52])).

fof(f150,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f149,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f149,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f148,f92])).

fof(f92,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f90,f46])).

fof(f148,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f147,f80])).

fof(f80,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f78,f46])).

fof(f147,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f146,f42])).

fof(f146,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f145,f43])).

fof(f145,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f144,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f56,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f143,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f134,f57])).

fof(f57,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f134,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f68,f59])).

fof(f59,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f292,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4)) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f291,f52])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f290,f42])).

fof(f290,plain,(
    ! [X0,X1] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f289,f43])).

fof(f289,plain,(
    ! [X0,X1] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f288,f44])).

fof(f288,plain,(
    ! [X0,X1] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f287,f179])).

fof(f179,plain,(
    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f57,f177])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f189,f181])).

fof(f181,plain,(
    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f59,f177])).

fof(f189,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X5),u1_struct_0(X6))
      | k3_tmap_1(X7,X6,X5,X4,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X5,X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(forward_demodulation,[],[f188,f177])).

fof(f188,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X5),u1_struct_0(X6))
      | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ m1_pre_topc(X4,X5)
      | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4))
      | ~ m1_pre_topc(X5,X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(forward_demodulation,[],[f185,f177])).

fof(f185,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ m1_pre_topc(X4,X5)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X5),u1_struct_0(X6))
      | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4))
      | ~ m1_pre_topc(X5,X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(backward_demodulation,[],[f164,f177])).

fof(f164,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X5),u1_struct_0(X6))
      | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4))
      | ~ m1_pre_topc(X5,X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f161,f70])).

fof(f161,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X5),u1_struct_0(X6))
      | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f62,f56])).

fof(f251,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f250,f42])).

fof(f250,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f249,f43])).

fof(f249,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f248,f44])).

fof(f248,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f247,f179])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f187,f181])).

fof(f187,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X4),u1_struct_0(X5))
      | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k2_tmap_1(sK3,sK1,sK5,sK2)))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(forward_demodulation,[],[f186,f177])).

fof(f186,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X4),u1_struct_0(X5))
      | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(forward_demodulation,[],[f182,f177])).

fof(f182,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4),u1_struct_0(X5))
      | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(backward_demodulation,[],[f126,f177])).

fof(f126,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4),u1_struct_0(X5))
      | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(X4,X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f73,f56])).

fof(f389,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f388,f330])).

fof(f330,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f329,f39])).

fof(f329,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f328,f40])).

fof(f328,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f327,f41])).

fof(f327,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f326,f42])).

fof(f326,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f325,f43])).

fof(f325,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f324,f44])).

fof(f324,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f323,f45])).

fof(f323,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f322,f46])).

fof(f322,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f321,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f321,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f320,f50])).

fof(f320,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f319,f178])).

fof(f178,plain,(
    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(backward_demodulation,[],[f56,f177])).

fof(f319,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f318,f179])).

fof(f318,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f317,f180])).

fof(f180,plain,(
    v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) ),
    inference(backward_demodulation,[],[f58,f177])).

fof(f58,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f317,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f316,f181])).

fof(f316,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f304,f52])).

fof(f304,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f298])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

fof(f388,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f387,f341])).

fof(f341,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f340,f39])).

fof(f340,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f339,f40])).

fof(f339,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f338,f41])).

fof(f338,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f337,f42])).

fof(f337,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f336,f43])).

fof(f336,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f335,f44])).

fof(f335,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f334,f46])).

fof(f334,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f333,f50])).

fof(f333,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f332,f178])).

fof(f332,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f331,f179])).

fof(f331,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f305,f181])).

fof(f305,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f75,f298])).

fof(f387,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f386,f208])).

fof(f386,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f385,f232])).

fof(f385,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f384,f220])).

fof(f384,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(resolution,[],[f383,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

% (8590)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f1,axiom,(
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

fof(f383,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f382,f47])).

fof(f382,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f381,f93])).

fof(f381,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f380,f81])).

fof(f380,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f379,f42])).

fof(f379,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f378,f43])).

fof(f378,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f377,f44])).

fof(f377,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f376,f49])).

fof(f376,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f375,f45])).

fof(f375,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f374,f51])).

fof(f374,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f373,f53])).

fof(f373,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f372,f54])).

fof(f372,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f371,f55])).

fof(f371,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f367,f52])).

fof(f367,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f77,f301])).

fof(f301,plain,(
    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f300,f47])).

fof(f300,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f299,f93])).

fof(f299,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f295,f81])).

fof(f295,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f293,f51])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f70])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f310,plain,(
    v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f309,f39])).

fof(f309,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f308,f40])).

fof(f308,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f307,f41])).

fof(f307,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f302,f46])).

fof(f302,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f274,f298])).

fof(f274,plain,(
    ! [X0] :
      ( v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),sK4,sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f273,f49])).

fof(f273,plain,(
    ! [X0] :
      ( v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),sK4,sK1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f272,f52])).

fof(f272,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f271,f70])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f270,f42])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f269,f43])).

fof(f269,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f268,f44])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f267,f45])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f266,f178])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f265,f179])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f264,f181])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f65,f180])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8583)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.48  % (8578)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (8591)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (8579)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (8595)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (8594)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (8592)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (8587)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (8580)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (8584)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (8598)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (8586)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (8589)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (8576)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (8581)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (8601)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.32/0.53  % (8585)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.32/0.53  % (8597)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.32/0.53  % (8577)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (8599)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.32/0.54  % (8596)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.54  % (8600)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.55  % (8579)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f404,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(subsumption_resolution,[],[f395,f233])).
% 1.32/0.55  fof(f233,plain,(
% 1.32/0.55    ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f221,f232])).
% 1.32/0.55  fof(f232,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f231,f39])).
% 1.32/0.55  fof(f39,plain,(
% 1.32/0.55    ~v2_struct_0(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  % (8588)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.32/0.55  % (8593)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ((((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f36,f35,f34,f33,f32,f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f13,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f12])).
% 1.32/0.55  fof(f12,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & (m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f11])).
% 1.32/0.55  fof(f11,negated_conjecture,(
% 1.32/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 1.32/0.55    inference(negated_conjecture,[],[f10])).
% 1.32/0.55  fof(f10,conjecture,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_tmap_1)).
% 1.32/0.55  fof(f231,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f230,f40])).
% 1.32/0.55  fof(f40,plain,(
% 1.32/0.55    v2_pre_topc(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f230,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f229,f41])).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    l1_pre_topc(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f229,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f228,f42])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ~v2_struct_0(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f228,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f227,f43])).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    v2_pre_topc(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f227,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f226,f44])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    l1_pre_topc(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f226,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f225,f48])).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    m1_pre_topc(sK3,sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f225,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f224,f50])).
% 1.32/0.55  fof(f50,plain,(
% 1.32/0.55    m1_pre_topc(sK4,sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f224,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f223,f53])).
% 1.32/0.55  fof(f53,plain,(
% 1.32/0.55    v1_funct_1(sK5)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f223,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f222,f54])).
% 1.32/0.55  fof(f54,plain,(
% 1.32/0.55    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f222,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f203,f55])).
% 1.32/0.55  fof(f55,plain,(
% 1.32/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f203,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f74,f190])).
% 1.32/0.55  fof(f190,plain,(
% 1.32/0.55    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4)),
% 1.32/0.55    inference(forward_demodulation,[],[f176,f152])).
% 1.32/0.55  fof(f152,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 1.32/0.55    inference(resolution,[],[f142,f120])).
% 1.32/0.55  fof(f120,plain,(
% 1.32/0.55    m1_pre_topc(sK4,sK3)),
% 1.32/0.55    inference(resolution,[],[f119,f52])).
% 1.32/0.55  fof(f52,plain,(
% 1.32/0.55    m1_pre_topc(sK4,sK2)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f119,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK3)) )),
% 1.32/0.55    inference(resolution,[],[f111,f51])).
% 1.32/0.55  fof(f51,plain,(
% 1.32/0.55    m1_pre_topc(sK2,sK3)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f111,plain,(
% 1.32/0.55    ( ! [X6,X7] : (~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,X7) | m1_pre_topc(X6,sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f106,f93])).
% 1.32/0.55  fof(f93,plain,(
% 1.32/0.55    v2_pre_topc(sK3)),
% 1.32/0.55    inference(resolution,[],[f90,f48])).
% 1.32/0.55  fof(f90,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f88,f41])).
% 1.32/0.55  fof(f88,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(X0)) )),
% 1.32/0.55    inference(resolution,[],[f69,f40])).
% 1.32/0.55  fof(f69,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.32/0.55  fof(f106,plain,(
% 1.32/0.55    ( ! [X6,X7] : (~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,sK3) | m1_pre_topc(X6,sK3) | ~v2_pre_topc(sK3)) )),
% 1.32/0.55    inference(resolution,[],[f70,f81])).
% 1.32/0.55  fof(f81,plain,(
% 1.32/0.55    l1_pre_topc(sK3)),
% 1.32/0.55    inference(resolution,[],[f78,f48])).
% 1.32/0.55  fof(f78,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.32/0.55    inference(resolution,[],[f61,f41])).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f14])).
% 1.32/0.55  fof(f14,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.32/0.55  fof(f70,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.32/0.55  fof(f142,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f141,f47])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    ~v2_struct_0(sK3)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f141,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f140,f93])).
% 1.32/0.55  fof(f140,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f139,f81])).
% 1.32/0.55  fof(f139,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f138,f42])).
% 1.32/0.55  fof(f138,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f137,f43])).
% 1.32/0.55  fof(f137,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f136,f44])).
% 1.32/0.55  fof(f136,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f135,f53])).
% 1.32/0.55  fof(f135,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f133,f54])).
% 1.32/0.55  fof(f133,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.32/0.55    inference(resolution,[],[f68,f55])).
% 1.32/0.55  fof(f68,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.32/0.55  fof(f176,plain,(
% 1.32/0.55    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 1.32/0.55    inference(resolution,[],[f174,f120])).
% 1.32/0.55  fof(f174,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f173,f39])).
% 1.32/0.55  fof(f173,plain,(
% 1.32/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f172,f40])).
% 1.32/0.55  fof(f172,plain,(
% 1.32/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f171,f41])).
% 1.32/0.55  fof(f171,plain,(
% 1.32/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(resolution,[],[f170,f48])).
% 1.32/0.55  fof(f170,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f169,f42])).
% 1.32/0.55  fof(f169,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f168,f43])).
% 1.32/0.55  fof(f168,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f167,f44])).
% 1.32/0.55  fof(f167,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f166,f54])).
% 1.32/0.55  fof(f166,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(resolution,[],[f163,f55])).
% 1.32/0.55  fof(f163,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X2)) | k3_tmap_1(X3,X2,X1,X0,sK5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f160,f70])).
% 1.32/0.55  fof(f160,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X2)) | k3_tmap_1(X3,X2,X1,X0,sK5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.32/0.55    inference(resolution,[],[f62,f53])).
% 1.32/0.55  fof(f62,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f5])).
% 1.32/0.55  fof(f5,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.32/0.55  fof(f74,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f30])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.32/0.55  fof(f221,plain,(
% 1.32/0.55    ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f209,f220])).
% 1.32/0.55  fof(f220,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.32/0.55    inference(subsumption_resolution,[],[f219,f39])).
% 1.32/0.55  fof(f219,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f218,f40])).
% 1.32/0.55  fof(f218,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f217,f41])).
% 1.32/0.55  fof(f217,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f216,f42])).
% 1.32/0.55  fof(f216,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f215,f43])).
% 1.32/0.55  fof(f215,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f214,f44])).
% 1.32/0.55  fof(f214,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f213,f48])).
% 1.32/0.55  fof(f213,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f212,f50])).
% 1.32/0.55  fof(f212,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f211,f53])).
% 1.32/0.55  fof(f211,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f210,f54])).
% 1.32/0.55  fof(f210,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f202,f55])).
% 1.32/0.55  fof(f202,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f75,f190])).
% 1.32/0.55  fof(f75,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f30])).
% 1.32/0.55  fof(f209,plain,(
% 1.32/0.55    ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f194,f208])).
% 1.32/0.55  fof(f208,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f207,f39])).
% 1.32/0.55  fof(f207,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f206,f40])).
% 1.32/0.55  fof(f206,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f205,f41])).
% 1.32/0.55  fof(f205,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f204,f48])).
% 1.32/0.55  fof(f204,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f201,f50])).
% 1.32/0.55  fof(f201,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f131,f190])).
% 1.32/0.55  fof(f131,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f130,f42])).
% 1.32/0.55  fof(f130,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f129,f43])).
% 1.32/0.55  fof(f129,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f128,f44])).
% 1.32/0.55  fof(f128,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f127,f54])).
% 1.32/0.55  fof(f127,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(resolution,[],[f125,f55])).
% 1.32/0.55  fof(f125,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK5)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.32/0.55    inference(resolution,[],[f73,f53])).
% 1.32/0.55  fof(f73,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f30])).
% 1.32/0.55  fof(f194,plain,(
% 1.32/0.55    ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))),
% 1.32/0.55    inference(forward_demodulation,[],[f193,f190])).
% 1.32/0.55  fof(f193,plain,(
% 1.32/0.55    ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.32/0.55    inference(forward_demodulation,[],[f192,f190])).
% 1.32/0.55  fof(f192,plain,(
% 1.32/0.55    ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.32/0.55    inference(forward_demodulation,[],[f191,f190])).
% 1.32/0.55  fof(f191,plain,(
% 1.32/0.55    ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.32/0.55    inference(backward_demodulation,[],[f60,f190])).
% 1.32/0.55  fof(f60,plain,(
% 1.32/0.55    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f395,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)),
% 1.32/0.55    inference(backward_demodulation,[],[f310,f390])).
% 1.32/0.55  fof(f390,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)),
% 1.32/0.55    inference(subsumption_resolution,[],[f389,f315])).
% 1.32/0.55  fof(f315,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f314,f39])).
% 1.32/0.55  fof(f314,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f313,f40])).
% 1.32/0.55  fof(f313,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f312,f41])).
% 1.32/0.55  fof(f312,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f311,f46])).
% 1.32/0.55  fof(f46,plain,(
% 1.32/0.55    m1_pre_topc(sK2,sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f311,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f303,f50])).
% 1.32/0.55  fof(f303,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f251,f298])).
% 1.32/0.55  fof(f298,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))),
% 1.32/0.55    inference(subsumption_resolution,[],[f297,f39])).
% 1.32/0.55  fof(f297,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f296,f40])).
% 1.32/0.55  fof(f296,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f294,f41])).
% 1.32/0.55  fof(f294,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(resolution,[],[f293,f46])).
% 1.32/0.55  fof(f293,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(sK2,X0) | k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(forward_demodulation,[],[f292,f184])).
% 1.32/0.55  fof(f184,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4))),
% 1.32/0.55    inference(backward_demodulation,[],[f153,f177])).
% 1.32/0.55  fof(f177,plain,(
% 1.32/0.55    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2)),
% 1.32/0.55    inference(forward_demodulation,[],[f175,f151])).
% 1.32/0.55  fof(f151,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2))),
% 1.32/0.55    inference(resolution,[],[f142,f51])).
% 1.32/0.55  fof(f175,plain,(
% 1.32/0.55    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2))),
% 1.32/0.55    inference(resolution,[],[f174,f51])).
% 1.32/0.55  fof(f153,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4))),
% 1.32/0.55    inference(resolution,[],[f150,f52])).
% 1.32/0.55  fof(f150,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f149,f45])).
% 1.32/0.55  fof(f45,plain,(
% 1.32/0.55    ~v2_struct_0(sK2)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f149,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f148,f92])).
% 1.32/0.55  fof(f92,plain,(
% 1.32/0.55    v2_pre_topc(sK2)),
% 1.32/0.55    inference(resolution,[],[f90,f46])).
% 1.32/0.55  fof(f148,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f147,f80])).
% 1.32/0.55  fof(f80,plain,(
% 1.32/0.55    l1_pre_topc(sK2)),
% 1.32/0.55    inference(resolution,[],[f78,f46])).
% 1.32/0.55  fof(f147,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f146,f42])).
% 1.32/0.55  fof(f146,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f145,f43])).
% 1.32/0.55  fof(f145,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f144,f44])).
% 1.32/0.55  fof(f144,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f143,f56])).
% 1.32/0.55  fof(f56,plain,(
% 1.32/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f143,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f134,f57])).
% 1.32/0.55  fof(f57,plain,(
% 1.32/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f134,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.32/0.55    inference(resolution,[],[f68,f59])).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f292,plain,(
% 1.32/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4)) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(resolution,[],[f291,f52])).
% 1.32/0.55  fof(f291,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f290,f42])).
% 1.32/0.55  fof(f290,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f289,f43])).
% 1.32/0.55  fof(f289,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f288,f44])).
% 1.32/0.55  fof(f288,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f287,f179])).
% 1.32/0.55  fof(f179,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.32/0.55    inference(backward_demodulation,[],[f57,f177])).
% 1.32/0.55  fof(f287,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X1)) = k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(resolution,[],[f189,f181])).
% 1.32/0.55  fof(f181,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.32/0.55    inference(backward_demodulation,[],[f59,f177])).
% 1.32/0.55  fof(f189,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X5),u1_struct_0(X6)) | k3_tmap_1(X7,X6,X5,X4,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X4)) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X5,X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.32/0.55    inference(forward_demodulation,[],[f188,f177])).
% 1.32/0.55  fof(f188,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X5),u1_struct_0(X6)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~m1_pre_topc(X4,X5) | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4)) | ~m1_pre_topc(X5,X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.32/0.55    inference(forward_demodulation,[],[f185,f177])).
% 1.32/0.55  fof(f185,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~m1_pre_topc(X4,X5) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X5),u1_struct_0(X6)) | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4)) | ~m1_pre_topc(X5,X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.32/0.55    inference(backward_demodulation,[],[f164,f177])).
% 1.32/0.55  fof(f164,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,X5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X5),u1_struct_0(X6)) | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4)) | ~m1_pre_topc(X5,X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f161,f70])).
% 1.32/0.55  fof(f161,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,X5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X5),u1_struct_0(X6)) | k3_tmap_1(X7,X6,X5,X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_partfun1(u1_struct_0(X5),u1_struct_0(X6),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4)) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.32/0.55    inference(resolution,[],[f62,f56])).
% 1.32/0.55  fof(f251,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f250,f42])).
% 1.32/0.55  fof(f250,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f249,f43])).
% 1.32/0.55  fof(f249,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f248,f44])).
% 1.32/0.55  fof(f248,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f247,f179])).
% 1.32/0.55  fof(f247,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,k2_tmap_1(sK3,sK1,sK5,sK2))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(resolution,[],[f187,f181])).
% 1.32/0.55  fof(f187,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X4),u1_struct_0(X5)) | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k2_tmap_1(sK3,sK1,sK5,sK2))) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X4,X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.32/0.55    inference(forward_demodulation,[],[f186,f177])).
% 1.32/0.55  fof(f186,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X4),u1_struct_0(X5)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X4,X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.32/0.55    inference(forward_demodulation,[],[f182,f177])).
% 1.32/0.55  fof(f182,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4),u1_struct_0(X5)) | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X4,X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.32/0.55    inference(backward_demodulation,[],[f126,f177])).
% 1.32/0.55  fof(f126,plain,(
% 1.32/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X4),u1_struct_0(X5)) | v1_funct_1(k3_tmap_1(X6,X5,X4,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(X4,X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.32/0.55    inference(resolution,[],[f73,f56])).
% 1.32/0.55  fof(f389,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f388,f330])).
% 1.32/0.55  fof(f330,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f329,f39])).
% 1.32/0.55  fof(f329,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f328,f40])).
% 1.32/0.55  fof(f328,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f327,f41])).
% 1.32/0.55  fof(f327,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f326,f42])).
% 1.32/0.55  fof(f326,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f325,f43])).
% 1.32/0.55  fof(f325,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f324,f44])).
% 1.32/0.55  fof(f324,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f323,f45])).
% 1.32/0.55  fof(f323,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f322,f46])).
% 1.32/0.55  fof(f322,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f321,f49])).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    ~v2_struct_0(sK4)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f321,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f320,f50])).
% 1.32/0.55  fof(f320,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f319,f178])).
% 1.32/0.55  fof(f178,plain,(
% 1.32/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))),
% 1.32/0.55    inference(backward_demodulation,[],[f56,f177])).
% 1.32/0.55  fof(f319,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f318,f179])).
% 1.32/0.55  fof(f318,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f317,f180])).
% 1.32/0.55  fof(f180,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1)),
% 1.32/0.55    inference(backward_demodulation,[],[f58,f177])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f37])).
% 1.32/0.55  fof(f317,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f316,f181])).
% 1.32/0.55  fof(f316,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f304,f52])).
% 1.32/0.55  fof(f304,plain,(
% 1.32/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK2) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f64,f298])).
% 1.32/0.55  fof(f64,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  fof(f18,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f17])).
% 1.32/0.55  fof(f17,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f9])).
% 1.32/0.55  fof(f9,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).
% 1.32/0.55  fof(f388,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f387,f341])).
% 1.32/0.55  fof(f341,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.32/0.55    inference(subsumption_resolution,[],[f340,f39])).
% 1.32/0.55  fof(f340,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f339,f40])).
% 1.32/0.55  fof(f339,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f338,f41])).
% 1.32/0.55  fof(f338,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f337,f42])).
% 1.32/0.55  fof(f337,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f336,f43])).
% 1.32/0.55  fof(f336,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f335,f44])).
% 1.32/0.55  fof(f335,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f334,f46])).
% 1.32/0.55  fof(f334,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f333,f50])).
% 1.32/0.55  fof(f333,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f332,f178])).
% 1.32/0.55  fof(f332,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f331,f179])).
% 1.32/0.55  fof(f331,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f305,f181])).
% 1.32/0.55  fof(f305,plain,(
% 1.32/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f75,f298])).
% 1.32/0.55  fof(f387,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f386,f208])).
% 1.32/0.55  fof(f386,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f385,f232])).
% 1.32/0.55  fof(f385,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f384,f220])).
% 1.32/0.55  fof(f384,plain,(
% 1.32/0.55    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 1.32/0.55    inference(resolution,[],[f383,f71])).
% 1.32/0.55  fof(f71,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f38])).
% 1.32/0.55  fof(f38,plain,(
% 1.32/0.55    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.32/0.55    inference(nnf_transformation,[],[f28])).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.32/0.55    inference(flattening,[],[f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.32/0.55    inference(ennf_transformation,[],[f1])).
% 1.32/0.55  % (8590)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.32/0.55  fof(f383,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4))),
% 1.32/0.55    inference(subsumption_resolution,[],[f382,f47])).
% 1.32/0.55  fof(f382,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f381,f93])).
% 1.32/0.55  fof(f381,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f380,f81])).
% 1.32/0.55  fof(f380,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f379,f42])).
% 1.32/0.55  fof(f379,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f378,f43])).
% 1.32/0.55  fof(f378,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f377,f44])).
% 1.32/0.55  fof(f377,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f376,f49])).
% 1.32/0.55  fof(f376,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f375,f45])).
% 1.32/0.55  fof(f375,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | v2_struct_0(sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f374,f51])).
% 1.32/0.55  fof(f374,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f373,f53])).
% 1.32/0.55  fof(f373,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f372,f54])).
% 1.32/0.55  fof(f372,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f371,f55])).
% 1.32/0.55  fof(f371,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f367,f52])).
% 1.32/0.55  fof(f367,plain,(
% 1.32/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK4,sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(superposition,[],[f77,f301])).
% 1.32/0.55  fof(f301,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))),
% 1.32/0.55    inference(subsumption_resolution,[],[f300,f47])).
% 1.32/0.55  fof(f300,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f299,f93])).
% 1.32/0.55  fof(f299,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f295,f81])).
% 1.32/0.55  fof(f295,plain,(
% 1.32/0.55    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.32/0.55    inference(resolution,[],[f293,f51])).
% 1.32/0.55  fof(f77,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f67,f70])).
% 1.32/0.55  fof(f67,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f20])).
% 1.32/0.55  fof(f20,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f19])).
% 1.32/0.55  fof(f19,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f7])).
% 1.32/0.55  fof(f7,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).
% 1.32/0.55  fof(f310,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f309,f39])).
% 1.32/0.55  fof(f309,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f308,f40])).
% 1.32/0.55  fof(f308,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f307,f41])).
% 1.32/0.55  fof(f307,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f302,f46])).
% 1.32/0.55  fof(f302,plain,(
% 1.32/0.55    v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(superposition,[],[f274,f298])).
% 1.32/0.55  fof(f274,plain,(
% 1.32/0.55    ( ! [X0] : (v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),sK4,sK1) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f273,f49])).
% 1.32/0.55  fof(f273,plain,(
% 1.32/0.55    ( ! [X0] : (v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),sK4,sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(resolution,[],[f272,f52])).
% 1.32/0.55  fof(f272,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f271,f70])).
% 1.32/0.55  fof(f271,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f270,f42])).
% 1.32/0.55  fof(f270,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f269,f43])).
% 1.32/0.55  fof(f269,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f268,f44])).
% 1.32/0.55  fof(f268,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f267,f45])).
% 1.55/0.56  fof(f267,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f266,f178])).
% 1.55/0.56  fof(f266,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f265,f179])).
% 1.55/0.56  fof(f265,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f264,f181])).
% 1.55/0.56  fof(f264,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),X0,sK1) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.55/0.56    inference(resolution,[],[f65,f180])).
% 1.55/0.56  fof(f65,plain,(
% 1.55/0.56    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,X2,X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f18])).
% 1.55/0.56  % SZS output end Proof for theBenchmark
% 1.55/0.56  % (8579)------------------------------
% 1.55/0.56  % (8579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (8579)Termination reason: Refutation
% 1.55/0.56  
% 1.55/0.56  % (8579)Memory used [KB]: 6652
% 1.55/0.56  % (8579)Time elapsed: 0.134 s
% 1.55/0.56  % (8579)------------------------------
% 1.55/0.56  % (8579)------------------------------
% 1.55/0.57  % (8575)Success in time 0.201 s
%------------------------------------------------------------------------------
