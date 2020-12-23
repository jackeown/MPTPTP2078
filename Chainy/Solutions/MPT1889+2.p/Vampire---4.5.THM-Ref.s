%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1889+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 4.23s
% Output     : Refutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 545 expanded)
%              Number of leaves         :    8 ( 228 expanded)
%              Depth                    :   10
%              Number of atoms          :  250 (5685 expanded)
%              Number of equality atoms :   21 ( 630 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8191,plain,(
    $false ),
    inference(global_subsumption,[],[f4975,f8162])).

fof(f8162,plain,(
    k6_domain_1(u1_struct_0(sK6),sK11(sK6,sK7)) != k9_subset_1(u1_struct_0(sK6),sK7,sK8(sK11(sK6,sK7))) ),
    inference(unit_resulting_resolution,[],[f4063,f4064,f4066,f4071,f4067,f4976,f7998,f4086])).

fof(f4086,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK11(X0,X1))
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3908])).

fof(f3908,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK11(X0,X1))
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK11(X0,X1),X1)
            & m1_subset_1(sK11(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f3739,f3907])).

fof(f3907,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK11(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK11(X0,X1),X1)
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3739,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3738])).

fof(f3738,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3692])).

fof(f3692,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(f7998,plain,(
    v3_pre_topc(sK8(sK11(sK6,sK7)),sK6) ),
    inference(unit_resulting_resolution,[],[f4064,f4066,f4065,f4977,f4976,f4302])).

fof(f4302,plain,(
    ! [X2,X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4054])).

fof(f4054,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK65(X0),X0)
            & v4_pre_topc(sK65(X0),X0)
            & m1_subset_1(sK65(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK65])],[f4052,f4053])).

fof(f4053,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK65(X0),X0)
        & v4_pre_topc(sK65(X0),X0)
        & m1_subset_1(sK65(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4052,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f4051])).

fof(f4051,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3854])).

fof(f3854,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3853])).

fof(f3853,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3677])).

fof(f3677,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f4977,plain,(
    v4_pre_topc(sK8(sK11(sK6,sK7)),sK6) ),
    inference(unit_resulting_resolution,[],[f4483,f4482,f4069])).

fof(f4069,plain,(
    ! [X2] :
      ( v4_pre_topc(sK8(X2),sK6)
      | ~ r2_hidden(X2,sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f3900])).

fof(f3900,plain,
    ( ~ v2_tex_2(sK7,sK6)
    & ! [X2] :
        ( ( k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),sK7,sK8(X2))
          & v4_pre_topc(sK8(X2),sK6)
          & m1_subset_1(sK8(X2),k1_zfmisc_1(u1_struct_0(sK6))) )
        | ~ r2_hidden(X2,sK7)
        | ~ m1_subset_1(X2,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v3_tdlat_3(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f3727,f3899,f3898,f3897])).

fof(f3897,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( ? [X3] :
                    ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK6)
          & ! [X2] :
              ( ? [X3] :
                  ( k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),X1,X3)
                  & v4_pre_topc(X3,sK6)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v3_tdlat_3(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3898,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK6)
        & ! [X2] :
            ( ? [X3] :
                ( k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),X1,X3)
                & v4_pre_topc(X3,sK6)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK6)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ~ v2_tex_2(sK7,sK6)
      & ! [X2] :
          ( ? [X3] :
              ( k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),sK7,X3)
              & v4_pre_topc(X3,sK6)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
          | ~ r2_hidden(X2,sK7)
          | ~ m1_subset_1(X2,u1_struct_0(sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f3899,plain,(
    ! [X2] :
      ( ? [X3] :
          ( k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),sK7,X3)
          & v4_pre_topc(X3,sK6)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
     => ( k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),sK7,sK8(X2))
        & v4_pre_topc(sK8(X2),sK6)
        & m1_subset_1(sK8(X2),k1_zfmisc_1(u1_struct_0(sK6))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3727,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3726])).

fof(f3726,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3715])).

fof(f3715,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3714])).

fof(f3714,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

fof(f4482,plain,(
    m1_subset_1(sK11(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f4063,f4064,f4066,f4071,f4067,f4084])).

fof(f4084,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3908])).

fof(f4483,plain,(
    r2_hidden(sK11(sK6,sK7),sK7) ),
    inference(unit_resulting_resolution,[],[f4063,f4064,f4066,f4071,f4067,f4085])).

fof(f4085,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | r2_hidden(sK11(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f3908])).

fof(f4065,plain,(
    v3_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4976,plain,(
    m1_subset_1(sK8(sK11(sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unit_resulting_resolution,[],[f4483,f4482,f4068])).

fof(f4068,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(X2),k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ r2_hidden(X2,sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4067,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4071,plain,(
    ~ v2_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4066,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4064,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4063,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4975,plain,(
    k6_domain_1(u1_struct_0(sK6),sK11(sK6,sK7)) = k9_subset_1(u1_struct_0(sK6),sK7,sK8(sK11(sK6,sK7))) ),
    inference(unit_resulting_resolution,[],[f4483,f4482,f4070])).

fof(f4070,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK6))
      | ~ r2_hidden(X2,sK7)
      | k6_domain_1(u1_struct_0(sK6),X2) = k9_subset_1(u1_struct_0(sK6),sK7,sK8(X2)) ) ),
    inference(cnf_transformation,[],[f3900])).
%------------------------------------------------------------------------------
