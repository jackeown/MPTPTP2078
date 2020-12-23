%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 287 expanded)
%              Number of leaves         :   35 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  486 ( 891 expanded)
%              Number of equality atoms :   42 (  92 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f89,f96,f107,f287,f293,f305,f314,f319,f324,f373,f382,f753,f761,f780,f787,f793,f809,f815,f821,f853])).

fof(f853,plain,
    ( ~ spl2_1
    | spl2_53 ),
    inference(avatar_split_clause,[],[f848,f806,f55])).

fof(f55,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f806,plain,
    ( spl2_53
  <=> v1_tops_2(u1_pre_topc(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f848,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_53 ),
    inference(resolution,[],[f808,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

fof(f808,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | spl2_53 ),
    inference(avatar_component_clause,[],[f806])).

fof(f821,plain,
    ( ~ spl2_5
    | ~ spl2_24
    | ~ spl2_7
    | spl2_29 ),
    inference(avatar_split_clause,[],[f817,f327,f94,f280,f75])).

fof(f75,plain,
    ( spl2_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f280,plain,
    ( spl2_24
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f94,plain,
    ( spl2_7
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f327,plain,
    ( spl2_29
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f817,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl2_7
    | spl2_29 ),
    inference(resolution,[],[f329,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f329,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f327])).

fof(f815,plain,
    ( ~ spl2_1
    | ~ spl2_29
    | spl2_52 ),
    inference(avatar_split_clause,[],[f814,f802,f327,f55])).

fof(f802,plain,
    ( spl2_52
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f814,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_52 ),
    inference(resolution,[],[f804,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f804,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl2_52 ),
    inference(avatar_component_clause,[],[f802])).

fof(f809,plain,
    ( ~ spl2_52
    | ~ spl2_53
    | ~ spl2_49
    | ~ spl2_1
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f798,f785,f55,f777,f806,f802])).

fof(f777,plain,
    ( spl2_49
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f785,plain,
    ( spl2_50
  <=> ! [X0] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f798,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_50 ),
    inference(resolution,[],[f786,f57])).

fof(f57,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f786,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f785])).

fof(f793,plain,
    ( ~ spl2_1
    | spl2_49 ),
    inference(avatar_split_clause,[],[f789,f777,f55])).

fof(f789,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_49 ),
    inference(resolution,[],[f779,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f779,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_49 ),
    inference(avatar_component_clause,[],[f777])).

fof(f787,plain,
    ( spl2_50
    | ~ spl2_49
    | ~ spl2_25
    | spl2_48 ),
    inference(avatar_split_clause,[],[f783,f773,f284,f777,f785])).

fof(f284,plain,
    ( spl2_25
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f773,plain,
    ( spl2_48
  <=> v1_tops_2(u1_pre_topc(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f783,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_25
    | spl2_48 ),
    inference(forward_demodulation,[],[f781,f286])).

fof(f286,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f284])).

fof(f781,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ l1_pre_topc(X0) )
    | spl2_48 ),
    inference(resolution,[],[f775,f51])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | X1 != X3
      | v1_tops_2(X3,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f775,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | spl2_48 ),
    inference(avatar_component_clause,[],[f773])).

fof(f780,plain,
    ( ~ spl2_48
    | ~ spl2_5
    | ~ spl2_49
    | ~ spl2_25
    | spl2_46 ),
    inference(avatar_split_clause,[],[f771,f758,f284,f777,f75,f773])).

fof(f758,plain,
    ( spl2_46
  <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f771,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ spl2_25
    | spl2_46 ),
    inference(forward_demodulation,[],[f770,f286])).

fof(f770,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | spl2_46 ),
    inference(resolution,[],[f760,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f760,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | spl2_46 ),
    inference(avatar_component_clause,[],[f758])).

fof(f761,plain,
    ( ~ spl2_5
    | ~ spl2_46
    | spl2_32
    | ~ spl2_34
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f754,f751,f379,f370,f758,f75])).

fof(f370,plain,
    ( spl2_32
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f379,plain,
    ( spl2_34
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f751,plain,
    ( spl2_45
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK1)
        | u1_pre_topc(sK0) = X1
        | ~ r1_tarski(u1_pre_topc(sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f754,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl2_45 ),
    inference(resolution,[],[f752,f35])).

fof(f752,plain,
    ( ! [X1] :
        ( ~ v1_tops_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_pre_topc(sK0) = X1
        | ~ r1_tarski(u1_pre_topc(sK0),X1) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f751])).

fof(f753,plain,
    ( ~ spl2_26
    | spl2_45
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f749,f284,f75,f55,f751,f290])).

fof(f290,plain,
    ( spl2_26
  <=> m1_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f749,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(u1_pre_topc(sK0),X1)
        | u1_pre_topc(sK0) = X1
        | ~ m1_pre_topc(sK0,sK1)
        | ~ v1_tops_2(X1,sK1) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_25 ),
    inference(duplicate_literal_removal,[],[f748])).

fof(f748,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(u1_pre_topc(sK0),X1)
        | u1_pre_topc(sK0) = X1
        | ~ m1_pre_topc(sK0,sK1)
        | ~ v1_tops_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f745,f286])).

fof(f745,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_pre_topc(sK0),X1)
        | u1_pre_topc(sK0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK0,sK1)
        | ~ v1_tops_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(resolution,[],[f238,f77])).

fof(f77,plain,
    ( l1_pre_topc(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ r1_tarski(u1_pre_topc(sK0),X0)
        | u1_pre_topc(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_pre_topc(sK0,X1)
        | ~ v1_tops_2(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_1 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(u1_pre_topc(sK0),X0)
        | u1_pre_topc(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_pre_topc(sK0,X1)
        | ~ v1_tops_2(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(X1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f186,f51])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(u1_pre_topc(sK0),X0)
        | u1_pre_topc(sK0) = X0 )
    | ~ spl2_1 ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(X0,X1)
      | ~ r1_tarski(u1_pre_topc(X1),X0)
      | u1_pre_topc(X1) = X0 ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f382,plain,
    ( ~ spl2_5
    | spl2_34
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f362,f284,f379,f75])).

fof(f362,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ spl2_25 ),
    inference(superposition,[],[f36,f286])).

fof(f373,plain,
    ( spl2_2
    | ~ spl2_5
    | ~ spl2_32
    | ~ spl2_6
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f368,f284,f86,f370,f75,f60])).

fof(f60,plain,
    ( spl2_2
  <=> v2_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f86,plain,
    ( spl2_6
  <=> u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f368,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_tdlat_3(sK1)
    | ~ spl2_6
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f359,f88])).

fof(f88,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f359,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_tdlat_3(sK1)
    | ~ spl2_25 ),
    inference(superposition,[],[f37,f286])).

fof(f37,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f324,plain,
    ( ~ spl2_5
    | spl2_24 ),
    inference(avatar_split_clause,[],[f321,f280,f75])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK1)
    | spl2_24 ),
    inference(resolution,[],[f282,f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f282,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl2_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f319,plain,
    ( ~ spl2_1
    | spl2_28 ),
    inference(avatar_split_clause,[],[f316,f311,f55])).

fof(f311,plain,
    ( spl2_28
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f316,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_28 ),
    inference(resolution,[],[f313,f34])).

fof(f313,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( ~ spl2_28
    | ~ spl2_1
    | spl2_27 ),
    inference(avatar_split_clause,[],[f309,f302,f55,f311])).

fof(f302,plain,
    ( spl2_27
  <=> m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f309,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | spl2_27 ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | spl2_27 ),
    inference(resolution,[],[f304,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f304,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f302])).

fof(f305,plain,
    ( ~ spl2_5
    | ~ spl2_27
    | ~ spl2_4
    | spl2_26 ),
    inference(avatar_split_clause,[],[f300,f290,f70,f302,f75])).

fof(f70,plain,
    ( spl2_4
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f300,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl2_4
    | spl2_26 ),
    inference(forward_demodulation,[],[f299,f72])).

fof(f72,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f299,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl2_26 ),
    inference(resolution,[],[f292,f47])).

fof(f292,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | spl2_26 ),
    inference(avatar_component_clause,[],[f290])).

fof(f293,plain,
    ( ~ spl2_5
    | ~ spl2_26
    | spl2_23 ),
    inference(avatar_split_clause,[],[f288,f276,f290,f75])).

fof(f276,plain,
    ( spl2_23
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f288,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | spl2_23 ),
    inference(resolution,[],[f278,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f278,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f276])).

fof(f287,plain,
    ( ~ spl2_23
    | ~ spl2_24
    | spl2_25
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f273,f105,f94,f75,f284,f280,f276])).

fof(f105,plain,
    ( spl2_8
  <=> ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | u1_struct_0(X0) = u1_struct_0(sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f273,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(resolution,[],[f115,f77])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = u1_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) )
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(resolution,[],[f106,f95])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
        | u1_struct_0(X0) = u1_struct_0(sK0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( ~ spl2_1
    | spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f103,f55,f105,f55])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
        | u1_struct_0(X0) = u1_struct_0(sK0)
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f99,f47])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
        | u1_struct_0(X0) = u1_struct_0(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f82,f57])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(resolution,[],[f42,f50])).

fof(f96,plain,
    ( ~ spl2_5
    | spl2_7
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f92,f70,f94,f75])).

fof(f92,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl2_4 ),
    inference(superposition,[],[f40,f72])).

% (26755)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f89,plain,
    ( ~ spl2_1
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f84,f65,f86,f55])).

fof(f65,plain,
    ( spl2_3
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f84,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f38,f67])).

fof(f67,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (26758)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (26749)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (26749)Refutation not found, incomplete strategy% (26749)------------------------------
% 0.21/0.49  % (26749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26749)Memory used [KB]: 10618
% 0.21/0.49  % (26749)Time elapsed: 0.089 s
% 0.21/0.49  % (26749)------------------------------
% 0.21/0.49  % (26749)------------------------------
% 0.21/0.50  % (26747)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (26744)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (26763)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (26746)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (26758)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (26745)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f863,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f89,f96,f107,f287,f293,f305,f314,f319,f324,f373,f382,f753,f761,f780,f787,f793,f809,f815,f821,f853])).
% 0.21/0.51  fof(f853,plain,(
% 0.21/0.51    ~spl2_1 | spl2_53),
% 0.21/0.51    inference(avatar_split_clause,[],[f848,f806,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl2_1 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f806,plain,(
% 0.21/0.51    spl2_53 <=> v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.51  fof(f848,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | spl2_53),
% 0.21/0.51    inference(resolution,[],[f808,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).
% 0.21/0.51  fof(f808,plain,(
% 0.21/0.51    ~v1_tops_2(u1_pre_topc(sK0),sK0) | spl2_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f806])).
% 0.21/0.51  fof(f821,plain,(
% 0.21/0.51    ~spl2_5 | ~spl2_24 | ~spl2_7 | spl2_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f817,f327,f94,f280,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl2_5 <=> l1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    spl2_24 <=> m1_pre_topc(sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl2_7 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    spl2_29 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.51  fof(f817,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | (~spl2_7 | spl2_29)),
% 0.21/0.51    inference(resolution,[],[f329,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f327])).
% 0.21/0.51  fof(f815,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_29 | spl2_52),
% 0.21/0.51    inference(avatar_split_clause,[],[f814,f802,f327,f55])).
% 0.21/0.51  fof(f802,plain,(
% 0.21/0.51    spl2_52 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.21/0.51  fof(f814,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | spl2_52),
% 0.21/0.51    inference(resolution,[],[f804,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.51  fof(f804,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK0) | spl2_52),
% 0.21/0.51    inference(avatar_component_clause,[],[f802])).
% 0.21/0.51  fof(f809,plain,(
% 0.21/0.51    ~spl2_52 | ~spl2_53 | ~spl2_49 | ~spl2_1 | ~spl2_50),
% 0.21/0.51    inference(avatar_split_clause,[],[f798,f785,f55,f777,f806,f802])).
% 0.21/0.51  fof(f777,plain,(
% 0.21/0.51    spl2_49 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.51  fof(f785,plain,(
% 0.21/0.51    spl2_50 <=> ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(sK1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.51  fof(f798,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(u1_pre_topc(sK0),sK0) | ~m1_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_50)),
% 0.21/0.51    inference(resolution,[],[f786,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  fof(f786,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(sK1,X0)) ) | ~spl2_50),
% 0.21/0.51    inference(avatar_component_clause,[],[f785])).
% 0.21/0.51  fof(f793,plain,(
% 0.21/0.51    ~spl2_1 | spl2_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f789,f777,f55])).
% 0.21/0.51  fof(f789,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | spl2_49),
% 0.21/0.51    inference(resolution,[],[f779,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  fof(f779,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f777])).
% 0.21/0.51  fof(f787,plain,(
% 0.21/0.51    spl2_50 | ~spl2_49 | ~spl2_25 | spl2_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f783,f773,f284,f777,f785])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    spl2_25 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.51  fof(f773,plain,(
% 0.21/0.51    spl2_48 <=> v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.21/0.51  fof(f783,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(sK1,X0) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~l1_pre_topc(X0)) ) | (~spl2_25 | spl2_48)),
% 0.21/0.51    inference(forward_demodulation,[],[f781,f286])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f284])).
% 0.21/0.51  fof(f781,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(sK1,X0) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(X0)) ) | spl2_48),
% 0.21/0.51    inference(resolution,[],[f775,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | X1 != X3 | v1_tops_2(X3,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 0.21/0.51  fof(f775,plain,(
% 0.21/0.51    ~v1_tops_2(u1_pre_topc(sK0),sK1) | spl2_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f773])).
% 0.21/0.51  fof(f780,plain,(
% 0.21/0.51    ~spl2_48 | ~spl2_5 | ~spl2_49 | ~spl2_25 | spl2_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f771,f758,f284,f777,f75,f773])).
% 0.21/0.51  fof(f758,plain,(
% 0.21/0.51    spl2_46 <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.21/0.51  fof(f771,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~v1_tops_2(u1_pre_topc(sK0),sK1) | (~spl2_25 | spl2_46)),
% 0.21/0.51    inference(forward_demodulation,[],[f770,f286])).
% 0.21/0.51  fof(f770,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v1_tops_2(u1_pre_topc(sK0),sK1) | spl2_46),
% 0.21/0.51    inference(resolution,[],[f760,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tops_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.51  fof(f760,plain,(
% 0.21/0.51    ~r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | spl2_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f758])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    ~spl2_5 | ~spl2_46 | spl2_32 | ~spl2_34 | ~spl2_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f754,f751,f379,f370,f758,f75])).
% 0.21/0.51  fof(f370,plain,(
% 0.21/0.51    spl2_32 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    spl2_34 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.51  fof(f751,plain,(
% 0.21/0.51    spl2_45 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK1) | u1_pre_topc(sK0) = X1 | ~r1_tarski(u1_pre_topc(sK0),X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.51  fof(f754,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~spl2_45),
% 0.21/0.51    inference(resolution,[],[f752,f35])).
% 0.21/0.51  fof(f752,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_tops_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | u1_pre_topc(sK0) = X1 | ~r1_tarski(u1_pre_topc(sK0),X1)) ) | ~spl2_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f751])).
% 0.21/0.51  fof(f753,plain,(
% 0.21/0.51    ~spl2_26 | spl2_45 | ~spl2_1 | ~spl2_5 | ~spl2_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f749,f284,f75,f55,f751,f290])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    spl2_26 <=> m1_pre_topc(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.51  fof(f749,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(u1_pre_topc(sK0),X1) | u1_pre_topc(sK0) = X1 | ~m1_pre_topc(sK0,sK1) | ~v1_tops_2(X1,sK1)) ) | (~spl2_1 | ~spl2_5 | ~spl2_25)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f748])).
% 0.21/0.51  fof(f748,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(u1_pre_topc(sK0),X1) | u1_pre_topc(sK0) = X1 | ~m1_pre_topc(sK0,sK1) | ~v1_tops_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl2_1 | ~spl2_5 | ~spl2_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f745,f286])).
% 0.21/0.51  fof(f745,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(u1_pre_topc(sK0),X1) | u1_pre_topc(sK0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK1) | ~v1_tops_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl2_1 | ~spl2_5)),
% 0.21/0.51    inference(resolution,[],[f238,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~r1_tarski(u1_pre_topc(sK0),X0) | u1_pre_topc(sK0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(sK0,X1) | ~v1_tops_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f235])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(u1_pre_topc(sK0),X0) | u1_pre_topc(sK0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(sK0,X1) | ~v1_tops_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(X1)) ) | ~spl2_1),
% 0.21/0.51    inference(resolution,[],[f186,f51])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(u1_pre_topc(sK0),X0) | u1_pre_topc(sK0) = X0) ) | ~spl2_1),
% 0.21/0.51    inference(resolution,[],[f97,f57])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~v1_tops_2(X0,X1) | ~r1_tarski(u1_pre_topc(X1),X0) | u1_pre_topc(X1) = X0) )),
% 0.21/0.51    inference(resolution,[],[f45,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    ~spl2_5 | spl2_34 | ~spl2_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f362,f284,f379,f75])).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~spl2_25),
% 0.21/0.51    inference(superposition,[],[f36,f286])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    spl2_2 | ~spl2_5 | ~spl2_32 | ~spl2_6 | ~spl2_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f368,f284,f86,f370,f75,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl2_2 <=> v2_tdlat_3(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl2_6 <=> u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    u1_pre_topc(sK0) != u1_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_tdlat_3(sK1) | (~spl2_6 | ~spl2_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f359,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK1) | v2_tdlat_3(sK1) | ~spl2_25),
% 0.21/0.51    inference(superposition,[],[f37,f286])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_tdlat_3(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    ~spl2_5 | spl2_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f321,f280,f75])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | spl2_24),
% 0.21/0.51    inference(resolution,[],[f282,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ~m1_pre_topc(sK1,sK1) | spl2_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f280])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ~spl2_1 | spl2_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f316,f311,f55])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    spl2_28 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | spl2_28),
% 0.21/0.51    inference(resolution,[],[f313,f34])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    ~m1_pre_topc(sK0,sK0) | spl2_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f311])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    ~spl2_28 | ~spl2_1 | spl2_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f309,f302,f55,f311])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    spl2_27 <=> m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | spl2_27),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f307])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | spl2_27),
% 0.21/0.51    inference(resolution,[],[f304,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    ~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f302])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    ~spl2_5 | ~spl2_27 | ~spl2_4 | spl2_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f300,f290,f70,f302,f75])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl2_4 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    ~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | (~spl2_4 | spl2_26)),
% 0.21/0.51    inference(forward_demodulation,[],[f299,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | spl2_26),
% 0.21/0.51    inference(resolution,[],[f292,f47])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    ~m1_pre_topc(sK0,sK1) | spl2_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f290])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    ~spl2_5 | ~spl2_26 | spl2_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f288,f276,f290,f75])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl2_23 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.51  fof(f288,plain,(
% 0.21/0.51    ~m1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK1) | spl2_23),
% 0.21/0.51    inference(resolution,[],[f278,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | spl2_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f276])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    ~spl2_23 | ~spl2_24 | spl2_25 | ~spl2_5 | ~spl2_7 | ~spl2_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f273,f105,f94,f75,f284,f280,f276])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl2_8 <=> ! [X0] : (~r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | u1_struct_0(X0) = u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(sK1) | ~m1_pre_topc(sK1,sK1) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl2_5 | ~spl2_7 | ~spl2_8)),
% 0.21/0.51    inference(resolution,[],[f115,f77])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))) ) | (~spl2_7 | ~spl2_8)),
% 0.21/0.51    inference(resolution,[],[f106,f95])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0)) ) | ~spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~spl2_1 | spl2_8 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f55,f105,f55])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 0.21/0.51    inference(resolution,[],[f99,f47])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0)) ) | ~spl2_1),
% 0.21/0.51    inference(resolution,[],[f82,f57])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 0.21/0.51    inference(resolution,[],[f42,f50])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ~spl2_5 | spl2_7 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f92,f70,f94,f75])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1)) ) | ~spl2_4),
% 0.21/0.51    inference(superposition,[],[f40,f72])).
% 0.21/0.51  % (26755)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~spl2_1 | spl2_6 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f84,f65,f86,f55])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl2_3 <=> v2_tdlat_3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f38,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    v2_tdlat_3(sK0) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_tdlat_3(X0) | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f75])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f70])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f65])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v2_tdlat_3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f60])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v2_tdlat_3(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f55])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26758)------------------------------
% 0.21/0.51  % (26758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26758)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26758)Memory used [KB]: 6524
% 0.21/0.51  % (26758)Time elapsed: 0.097 s
% 0.21/0.51  % (26758)------------------------------
% 0.21/0.51  % (26758)------------------------------
% 0.21/0.51  % (26760)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (26742)Success in time 0.154 s
%------------------------------------------------------------------------------
