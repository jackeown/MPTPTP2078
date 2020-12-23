%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t59_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 482 expanded)
%              Number of leaves         :   27 ( 203 expanded)
%              Depth                    :   22
%              Number of atoms          :  764 (4771 expanded)
%              Number of equality atoms :   90 ( 530 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4646,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f272,f288,f692,f714,f4620,f4644])).

fof(f4644,plain,(
    ~ spl13_242 ),
    inference(avatar_contradiction_clause,[],[f4643])).

fof(f4643,plain,
    ( $false
    | ~ spl13_242 ),
    inference(subsumption_resolution,[],[f4628,f234])).

fof(f234,plain,(
    ~ v3_pre_topc(sK6(sK0,sK4),sK0) ),
    inference(subsumption_resolution,[],[f233,f92])).

fof(f92,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ~ v1_tops_2(sK4,sK0)
    & k9_relat_1(k3_funct_3(sK2),sK3) = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & v1_tops_2(sK3,sK1)
    & v5_pre_topc(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f38,f70,f69,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v1_tops_2(X4,X0)
                        & k9_relat_1(k3_funct_3(X2),X3) = X4
                        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                    & v1_tops_2(X3,X1)
                    & v5_pre_topc(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v1_tops_2(X4,sK0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
                  & v1_tops_2(X3,X1)
                  & v5_pre_topc(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v1_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v1_tops_2(X4,X0)
                    & k9_relat_1(k3_funct_3(X2),X3) = X4
                    & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(X3,sK1)
                & v5_pre_topc(X2,X0,sK1)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v1_tops_2(X4,X0)
                  & k9_relat_1(k3_funct_3(X2),X3) = X4
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X3,X1)
              & v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ v1_tops_2(X4,X0)
                & k9_relat_1(k3_funct_3(sK2),X3) = X4
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & v1_tops_2(X3,X1)
            & v5_pre_topc(sK2,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ v1_tops_2(X4,X0)
              & k9_relat_1(k3_funct_3(X2),X3) = X4
              & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X3,X1)
          & v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ? [X4] :
            ( ~ v1_tops_2(X4,X0)
            & k9_relat_1(k3_funct_3(X2),sK3) = X4
            & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK3,X1)
        & v5_pre_topc(X2,X0,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( ~ v1_tops_2(X4,X0)
          & k9_relat_1(k3_funct_3(X2),X3) = X4
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(sK4,X0)
        & k9_relat_1(k3_funct_3(X2),X3) = sK4
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v1_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v1_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v1_tops_2(X3,X1)
                        & v5_pre_topc(X2,X0,X1) )
                     => ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                         => ( k9_relat_1(k3_funct_3(X2),X3) = X4
                           => v1_tops_2(X4,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v1_tops_2(X3,X1)
                      & v5_pre_topc(X2,X0,X1) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ( k9_relat_1(k3_funct_3(X2),X3) = X4
                         => v1_tops_2(X4,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t59_tops_2)).

fof(f233,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK4),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f230,f103])).

fof(f103,plain,(
    ~ v1_tops_2(sK4,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f230,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK4),sK0)
    | v1_tops_2(sK4,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f119,f101])).

fof(f101,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(sK6(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK6(X0,X1),X0)
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f77,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',d1_tops_2)).

fof(f4628,plain,
    ( v3_pre_topc(sK6(sK0,sK4),sK0)
    | ~ spl13_242 ),
    inference(resolution,[],[f4619,f228])).

fof(f228,plain,(
    r2_hidden(sK6(sK0,sK4),sK4) ),
    inference(subsumption_resolution,[],[f227,f92])).

fof(f227,plain,
    ( r2_hidden(sK6(sK0,sK4),sK4)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f224,f103])).

fof(f224,plain,
    ( r2_hidden(sK6(sK0,sK4),sK4)
    | v1_tops_2(sK4,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f118,f101])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK6(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f4619,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v3_pre_topc(X0,sK0) )
    | ~ spl13_242 ),
    inference(avatar_component_clause,[],[f4618])).

fof(f4618,plain,
    ( spl13_242
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_242])])).

fof(f4620,plain,
    ( ~ spl13_25
    | ~ spl13_27
    | spl13_242
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f4616,f690,f4618,f263,f260])).

fof(f260,plain,
    ( spl13_25
  <=> ~ v1_relat_1(k3_funct_3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f263,plain,
    ( spl13_27
  <=> ~ v1_funct_1(k3_funct_3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f690,plain,
    ( spl13_66
  <=> ! [X0] :
        ( ~ v3_pre_topc(X0,sK1)
        | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f4616,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v3_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl13_66 ),
    inference(forward_demodulation,[],[f4615,f102])).

fof(f102,plain,(
    k9_relat_1(k3_funct_3(sK2),sK3) = sK4 ),
    inference(cnf_transformation,[],[f71])).

fof(f4615,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl13_66 ),
    inference(duplicate_literal_removal,[],[f4614])).

fof(f4614,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl13_66 ),
    inference(resolution,[],[f2729,f148])).

fof(f148,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK7(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK8(X0,X1,X2)) = sK7(X0,X1,X2)
                  & r2_hidden(sK8(X0,X1,X2),X1)
                  & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
                    & r2_hidden(sK9(X0,X1,X6),X1)
                    & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f81,f84,f83,f82])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X1,X2)) = X3
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
        & r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',d12_funct_1)).

fof(f2729,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),sK3)
        | v3_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0)) )
    | ~ spl13_66 ),
    inference(subsumption_resolution,[],[f2728,f181])).

fof(f181,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f138,f97])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',cc1_relset_1)).

fof(f2728,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X1,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),sK3)
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl13_66 ),
    inference(subsumption_resolution,[],[f1878,f95])).

fof(f95,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f1878,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X1,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),sK3)
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl13_66 ),
    inference(superposition,[],[f760,f597])).

fof(f597,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,sK9(k3_funct_3(X1),X2,X0)) = X0
      | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(X1),X2))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f596,f121])).

fof(f121,plain,(
    ! [X0] :
      ( v1_relat_1(k3_funct_3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',dt_k3_funct_3)).

fof(f596,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(k3_funct_3(X1),X2))
      | k10_relat_1(X1,sK9(k3_funct_3(X1),X2,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k3_funct_3(X1)) ) ),
    inference(subsumption_resolution,[],[f595,f122])).

fof(f122,plain,(
    ! [X0] :
      ( v1_funct_1(k3_funct_3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f595,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(k3_funct_3(X1),X2))
      | k10_relat_1(X1,sK9(k3_funct_3(X1),X2,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k3_funct_3(X1))
      | ~ v1_relat_1(k3_funct_3(X1)) ) ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(k3_funct_3(X1),X2))
      | k10_relat_1(X1,sK9(k3_funct_3(X1),X2,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(X1),X2))
      | ~ v1_funct_1(k3_funct_3(X1))
      | ~ v1_relat_1(k3_funct_3(X1)) ) ),
    inference(resolution,[],[f244,f149])).

fof(f149,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(k3_funct_3(X0),X1,X2),k1_relat_1(k3_funct_3(X0)))
      | ~ r2_hidden(X2,k9_relat_1(k3_funct_3(X0),X1))
      | k10_relat_1(X0,sK9(k3_funct_3(X0),X1,X2)) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f243,f121])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,sK9(k3_funct_3(X0),X1,X2)) = X2
      | ~ r2_hidden(X2,k9_relat_1(k3_funct_3(X0),X1))
      | ~ v1_relat_1(k3_funct_3(X0))
      | ~ r2_hidden(sK9(k3_funct_3(X0),X1,X2),k1_relat_1(k3_funct_3(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f241,f122])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,sK9(k3_funct_3(X0),X1,X2)) = X2
      | ~ r2_hidden(X2,k9_relat_1(k3_funct_3(X0),X1))
      | ~ v1_funct_1(k3_funct_3(X0))
      | ~ v1_relat_1(k3_funct_3(X0))
      | ~ r2_hidden(sK9(k3_funct_3(X0),X1,X2),k1_relat_1(k3_funct_3(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f147,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
       => k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t24_funct_3)).

fof(f147,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f760,plain,
    ( ! [X0] :
        ( v3_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl13_66 ),
    inference(subsumption_resolution,[],[f752,f282])).

fof(f282,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f281,f209])).

fof(f209,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f139,f98])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t4_subset)).

fof(f281,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f280,f94])).

fof(f94,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f280,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f276,f100])).

fof(f100,plain,(
    v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f276,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_tops_2(sK3,sK1)
      | v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f116,f98])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | v3_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f752,plain,
    ( ! [X0] :
        ( v3_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v3_pre_topc(X0,sK1)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl13_66 ),
    inference(resolution,[],[f691,f209])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v3_pre_topc(X0,sK1) )
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f690])).

fof(f714,plain,(
    ~ spl13_64 ),
    inference(avatar_contradiction_clause,[],[f713])).

fof(f713,plain,
    ( $false
    | ~ spl13_64 ),
    inference(subsumption_resolution,[],[f712,f93])).

fof(f93,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f712,plain,
    ( v2_struct_0(sK1)
    | ~ spl13_64 ),
    inference(subsumption_resolution,[],[f711,f151])).

fof(f151,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f107,f94])).

fof(f107,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',dt_l1_pre_topc)).

fof(f711,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl13_64 ),
    inference(subsumption_resolution,[],[f698,f104])).

fof(f104,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',fc1_xboole_0)).

fof(f698,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl13_64 ),
    inference(superposition,[],[f120,f688])).

fof(f688,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl13_64
  <=> k2_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',fc5_struct_0)).

fof(f692,plain,
    ( spl13_64
    | spl13_66 ),
    inference(avatar_split_clause,[],[f685,f690,f687])).

fof(f685,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_struct_0(sK1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(sK2,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f684,f92])).

fof(f684,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_struct_0(sK1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f683,f94])).

fof(f683,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_struct_0(sK1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f682,f95])).

fof(f682,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_struct_0(sK1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f681,f96])).

fof(f96,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f681,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_struct_0(sK1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f677,f99])).

fof(f99,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f677,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | k2_struct_0(sK1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f323,f97])).

fof(f323,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | v3_pre_topc(k10_relat_1(X2,X3),X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(k10_relat_1(X2,X3),X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(superposition,[],[f108,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',redefinition_k8_relset_1)).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v3_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v3_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t59_tops_2.p',t55_tops_2)).

fof(f288,plain,(
    spl13_27 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f286,f181])).

fof(f286,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f285,f95])).

fof(f285,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_27 ),
    inference(resolution,[],[f264,f122])).

fof(f264,plain,
    ( ~ v1_funct_1(k3_funct_3(sK2))
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f263])).

fof(f272,plain,(
    spl13_25 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f270,f181])).

fof(f270,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f269,f95])).

fof(f269,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_25 ),
    inference(resolution,[],[f261,f121])).

fof(f261,plain,
    ( ~ v1_relat_1(k3_funct_3(sK2))
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f260])).
%------------------------------------------------------------------------------
