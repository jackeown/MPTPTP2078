%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t111_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:03 EDT 2019

% Result     : Theorem 5.99s
% Output     : Refutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  273 (2029 expanded)
%              Number of leaves         :   53 ( 750 expanded)
%              Depth                    :   30
%              Number of atoms          : 1211 (18027 expanded)
%              Number of equality atoms :   36 ( 378 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f287,f5684,f5687,f5695,f5704,f5710,f5717,f5722,f5872,f18228,f18263,f22726,f22763,f22769,f140089,f140660,f184169])).

fof(f184169,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | spl12_5
    | ~ spl12_6
    | ~ spl12_204
    | ~ spl12_206
    | spl12_259
    | ~ spl12_260
    | ~ spl12_262
    | spl12_4499 ),
    inference(avatar_contradiction_clause,[],[f184168])).

fof(f184168,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_204
    | ~ spl12_206
    | ~ spl12_259
    | ~ spl12_260
    | ~ spl12_262
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184167,f22686])).

fof(f22686,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_259 ),
    inference(avatar_component_clause,[],[f22685])).

fof(f22685,plain,
    ( spl12_259
  <=> ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_259])])).

fof(f184167,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_204
    | ~ spl12_206
    | ~ spl12_260
    | ~ spl12_262
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184166,f22692])).

fof(f22692,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_260 ),
    inference(avatar_component_clause,[],[f22691])).

fof(f22691,plain,
    ( spl12_260
  <=> v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_260])])).

fof(f184166,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_204
    | ~ spl12_206
    | ~ spl12_262
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184165,f22698])).

fof(f22698,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_262 ),
    inference(avatar_component_clause,[],[f22697])).

fof(f22697,plain,
    ( spl12_262
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_262])])).

fof(f184165,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_204
    | ~ spl12_206
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184164,f167])).

fof(f167,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) )
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f139,f138,f137])).

fof(f137,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X2,k6_tmap_1(sK0,X1))
                | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f138,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK1)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2),X2,k6_tmap_1(X0,sK1))
              | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK1)))
              | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2)) )
            & r1_xboole_0(u1_struct_0(X2),sK1)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
          & r1_xboole_0(u1_struct_0(X2),X1)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2),sK2,k6_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2)) )
        & r1_xboole_0(u1_struct_0(sK2),X1)
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',t111_tmap_1)).

fof(f184164,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_204
    | ~ spl12_206
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184163,f18189])).

fof(f18189,plain,
    ( v2_pre_topc(sK2)
    | ~ spl12_204 ),
    inference(avatar_component_clause,[],[f18188])).

fof(f18188,plain,
    ( spl12_204
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_204])])).

fof(f184163,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_206
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184162,f18195])).

fof(f18195,plain,
    ( l1_pre_topc(sK2)
    | ~ spl12_206 ),
    inference(avatar_component_clause,[],[f18194])).

fof(f18194,plain,
    ( spl12_206
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_206])])).

fof(f184162,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184161,f6908])).

fof(f6908,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ spl12_0 ),
    inference(backward_demodulation,[],[f6893,f265])).

fof(f265,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl12_0
  <=> v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f6893,plain,(
    k7_tmap_1(sK0,o_0_0_xboole_0) = k7_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f6854,f622])).

fof(f622,plain,(
    m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f616,f289])).

fof(f289,plain,(
    ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(superposition,[],[f197,f256])).

fof(f256,plain,(
    ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f175,f172,f172])).

fof(f172,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',d2_xboole_0)).

fof(f175,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',t2_boole)).

fof(f197,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',commutativity_k3_xboole_0)).

fof(f616,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f606,f604])).

fof(f604,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(subsumption_resolution,[],[f598,f166])).

fof(f166,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f140])).

fof(f598,plain,(
    ! [X1] :
      ( k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f595,f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',redefinition_k9_subset_1)).

fof(f595,plain,(
    ! [X24] : k9_subset_1(u1_struct_0(sK0),X24,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X24) ),
    inference(resolution,[],[f234,f166])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',commutativity_k9_subset_1)).

fof(f606,plain,(
    ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f601,f166])).

fof(f601,plain,(
    ! [X1] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f232,f595])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',dt_k9_subset_1)).

fof(f6854,plain,(
    ! [X94] :
      ( ~ m1_subset_1(X94,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,sK1) = k7_tmap_1(sK0,X94) ) ),
    inference(resolution,[],[f4400,f166])).

fof(f4400,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k7_tmap_1(sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f4268,f4268])).

fof(f4268,plain,(
    ! [X0] :
      ( k7_tmap_1(sK0,X0) = k6_relat_1(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f4267,f163])).

fof(f163,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f140])).

fof(f4267,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_relat_1(u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f4264,f165])).

fof(f165,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f140])).

fof(f4264,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k7_tmap_1(sK0,X0) = k6_relat_1(u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f260,f164])).

fof(f164,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f140])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k7_tmap_1(X0,X1) = k6_relat_1(u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f185,f176])).

fof(f176,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',redefinition_k6_partfun1)).

fof(f185,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',d10_tmap_1)).

fof(f184161,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184160,f6909])).

fof(f6909,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_2 ),
    inference(backward_demodulation,[],[f6893,f271])).

fof(f271,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl12_2
  <=> v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f184160,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184159,f144501])).

fof(f144501,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_6 ),
    inference(forward_demodulation,[],[f283,f28306])).

fof(f28306,plain,(
    k7_tmap_1(sK0,o_0_0_xboole_0) = k7_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f166,f6973])).

fof(f6973,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,o_0_0_xboole_0) = k7_tmap_1(sK0,X0) ) ),
    inference(backward_demodulation,[],[f6958,f4268])).

fof(f6958,plain,(
    k7_tmap_1(sK0,o_0_0_xboole_0) = k6_relat_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f6950,f616])).

fof(f6950,plain,(
    ! [X1] :
      ( k7_tmap_1(sK0,o_0_0_xboole_0) = k6_relat_1(u1_struct_0(sK0))
      | ~ m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f6945,f4268])).

fof(f6945,plain,(
    ! [X6] : k7_tmap_1(sK0,o_0_0_xboole_0) = k7_tmap_1(sK0,k3_xboole_0(X6,sK1)) ),
    inference(forward_demodulation,[],[f6870,f6893])).

fof(f6870,plain,(
    ! [X6] : k7_tmap_1(sK0,sK1) = k7_tmap_1(sK0,k3_xboole_0(X6,sK1)) ),
    inference(resolution,[],[f6854,f616])).

fof(f283,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl12_6
  <=> m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f184159,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_5
    | ~ spl12_4499 ),
    inference(subsumption_resolution,[],[f184156,f6910])).

fof(f6910,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ spl12_5 ),
    inference(backward_demodulation,[],[f6893,f280])).

fof(f280,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl12_5
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f184156,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_4499 ),
    inference(resolution,[],[f180629,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f144,f145])).

fof(f145,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f144,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',t49_tmap_1)).

fof(f180629,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ spl12_4499 ),
    inference(forward_demodulation,[],[f140088,f28306])).

fof(f140088,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | ~ spl12_4499 ),
    inference(avatar_component_clause,[],[f140087])).

fof(f140087,plain,
    ( spl12_4499
  <=> ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4499])])).

fof(f140660,plain,
    ( ~ spl12_67
    | ~ spl12_69
    | ~ spl12_71
    | spl12_7
    | ~ spl12_62
    | ~ spl12_64
    | ~ spl12_72 ),
    inference(avatar_split_clause,[],[f140659,f5679,f5655,f5649,f285,f5676,f5670,f5664])).

fof(f5664,plain,
    ( spl12_67
  <=> ~ v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_67])])).

fof(f5670,plain,
    ( spl12_69
  <=> ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).

fof(f5676,plain,
    ( spl12_71
  <=> ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_71])])).

fof(f285,plain,
    ( spl12_7
  <=> ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f5649,plain,
    ( spl12_62
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f5655,plain,
    ( spl12_64
  <=> l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f5679,plain,
    ( spl12_72
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).

fof(f140659,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ spl12_7
    | ~ spl12_62
    | ~ spl12_64
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f140658,f5650])).

fof(f5650,plain,
    ( l1_struct_0(sK0)
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f5649])).

fof(f140658,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_64
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f140657,f5656])).

fof(f5656,plain,
    ( l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_64 ),
    inference(avatar_component_clause,[],[f5655])).

fof(f140657,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f140655,f5680])).

fof(f5680,plain,
    ( l1_struct_0(sK2)
    | ~ spl12_72 ),
    inference(avatar_component_clause,[],[f5679])).

fof(f140655,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7 ),
    inference(resolution,[],[f286,f249])).

fof(f249,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f132,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f131])).

fof(f131,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',dt_k2_tmap_1)).

fof(f286,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f285])).

fof(f140089,plain,
    ( spl12_4
    | ~ spl12_7
    | ~ spl12_4499
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f106034,f273,f267,f140087,f285,f276])).

fof(f276,plain,
    ( spl12_4
  <=> v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f267,plain,
    ( spl12_1
  <=> ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f273,plain,
    ( spl12_3
  <=> ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f106034,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f106032,f166])).

fof(f106032,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f25214,f169])).

fof(f169,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f140])).

fof(f25214,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(sK2),X0)
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2))
      | ~ m1_subset_1(sK4(k6_tmap_1(sK0,X0),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2)),u1_struct_0(sK2))
      | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))))
      | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK2,k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f25213,f163])).

fof(f25213,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2))
      | ~ m1_subset_1(sK4(k6_tmap_1(sK0,X0),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2)),u1_struct_0(sK2))
      | ~ r1_xboole_0(u1_struct_0(sK2),X0)
      | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK2,k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f25212,f164])).

fof(f25212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2))
      | ~ m1_subset_1(sK4(k6_tmap_1(sK0,X0),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2)),u1_struct_0(sK2))
      | ~ r1_xboole_0(u1_struct_0(sK2),X0)
      | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK2,k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f25211,f165])).

fof(f25211,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2))
      | ~ m1_subset_1(sK4(k6_tmap_1(sK0,X0),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2)),u1_struct_0(sK2))
      | ~ r1_xboole_0(u1_struct_0(sK2),X0)
      | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK2,k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f25208,f167])).

fof(f25208,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,X0)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2))
      | v2_struct_0(sK2)
      | ~ m1_subset_1(sK4(k6_tmap_1(sK0,X0),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2)),u1_struct_0(sK2))
      | ~ r1_xboole_0(u1_struct_0(sK2),X0)
      | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK2,k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f6801,f168])).

fof(f168,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f140])).

fof(f6801,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6800,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',cc1_pre_topc)).

fof(f6800,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6799,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',dt_m1_pre_topc)).

fof(f6799,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6798,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',dt_k6_tmap_1)).

fof(f6798,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6797,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',fc4_tmap_1)).

fof(f6797,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f6796,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f6796,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f6795])).

fof(f6795,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK4(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f191,f188])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',t109_tmap_1)).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f146])).

fof(f22769,plain,(
    ~ spl12_258 ),
    inference(avatar_contradiction_clause,[],[f22768])).

fof(f22768,plain,
    ( $false
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f22767,f163])).

fof(f22767,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f22766,f164])).

fof(f22766,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f22765,f165])).

fof(f22765,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f22764,f166])).

fof(f22764,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_258 ),
    inference(resolution,[],[f22689,f209])).

fof(f22689,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_258 ),
    inference(avatar_component_clause,[],[f22688])).

fof(f22688,plain,
    ( spl12_258
  <=> v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_258])])).

fof(f22763,plain,(
    spl12_263 ),
    inference(avatar_contradiction_clause,[],[f22762])).

fof(f22762,plain,
    ( $false
    | ~ spl12_263 ),
    inference(subsumption_resolution,[],[f22761,f163])).

fof(f22761,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_263 ),
    inference(subsumption_resolution,[],[f22760,f164])).

fof(f22760,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_263 ),
    inference(subsumption_resolution,[],[f22759,f165])).

fof(f22759,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_263 ),
    inference(subsumption_resolution,[],[f22757,f166])).

fof(f22757,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_263 ),
    inference(resolution,[],[f22701,f214])).

fof(f22701,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_263 ),
    inference(avatar_component_clause,[],[f22700])).

fof(f22700,plain,
    ( spl12_263
  <=> ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_263])])).

fof(f22726,plain,(
    spl12_261 ),
    inference(avatar_contradiction_clause,[],[f22725])).

fof(f22725,plain,
    ( $false
    | ~ spl12_261 ),
    inference(subsumption_resolution,[],[f22724,f163])).

fof(f22724,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_261 ),
    inference(subsumption_resolution,[],[f22723,f164])).

fof(f22723,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_261 ),
    inference(subsumption_resolution,[],[f22722,f165])).

fof(f22722,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_261 ),
    inference(subsumption_resolution,[],[f22720,f166])).

fof(f22720,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_261 ),
    inference(resolution,[],[f22695,f211])).

fof(f22695,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_261 ),
    inference(avatar_component_clause,[],[f22694])).

fof(f22694,plain,
    ( spl12_261
  <=> ~ v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_261])])).

fof(f18263,plain,(
    spl12_207 ),
    inference(avatar_contradiction_clause,[],[f18262])).

fof(f18262,plain,
    ( $false
    | ~ spl12_207 ),
    inference(subsumption_resolution,[],[f18261,f165])).

fof(f18261,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_207 ),
    inference(resolution,[],[f18260,f168])).

fof(f18260,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl12_207 ),
    inference(resolution,[],[f18198,f183])).

fof(f18198,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl12_207 ),
    inference(avatar_component_clause,[],[f18197])).

fof(f18197,plain,
    ( spl12_207
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_207])])).

fof(f18228,plain,(
    spl12_205 ),
    inference(avatar_contradiction_clause,[],[f18227])).

fof(f18227,plain,
    ( $false
    | ~ spl12_205 ),
    inference(subsumption_resolution,[],[f18226,f164])).

fof(f18226,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl12_205 ),
    inference(subsumption_resolution,[],[f18225,f165])).

fof(f18225,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl12_205 ),
    inference(resolution,[],[f18224,f168])).

fof(f18224,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl12_205 ),
    inference(resolution,[],[f18192,f193])).

fof(f18192,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl12_205 ),
    inference(avatar_component_clause,[],[f18191])).

fof(f18191,plain,
    ( spl12_205
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_205])])).

fof(f5872,plain,
    ( spl12_3
    | ~ spl12_62
    | ~ spl12_64
    | ~ spl12_66
    | ~ spl12_68
    | ~ spl12_70
    | ~ spl12_72 ),
    inference(avatar_contradiction_clause,[],[f5871])).

fof(f5871,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_62
    | ~ spl12_64
    | ~ spl12_66
    | ~ spl12_68
    | ~ spl12_70
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f5870,f5650])).

fof(f5870,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_64
    | ~ spl12_66
    | ~ spl12_68
    | ~ spl12_70
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f5869,f5656])).

fof(f5869,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_66
    | ~ spl12_68
    | ~ spl12_70
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f5868,f5662])).

fof(f5662,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ spl12_66 ),
    inference(avatar_component_clause,[],[f5661])).

fof(f5661,plain,
    ( spl12_66
  <=> v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_66])])).

fof(f5868,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_68
    | ~ spl12_70
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f5867,f5668])).

fof(f5668,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f5667])).

fof(f5667,plain,
    ( spl12_68
  <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f5867,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_70
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f5866,f5674])).

fof(f5674,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_70 ),
    inference(avatar_component_clause,[],[f5673])).

fof(f5673,plain,
    ( spl12_70
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f5866,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_72 ),
    inference(subsumption_resolution,[],[f5865,f5680])).

fof(f5865,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3 ),
    inference(resolution,[],[f248,f274])).

fof(f274,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f273])).

fof(f248,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f5722,plain,(
    spl12_73 ),
    inference(avatar_contradiction_clause,[],[f5721])).

fof(f5721,plain,
    ( $false
    | ~ spl12_73 ),
    inference(subsumption_resolution,[],[f5720,f165])).

fof(f5720,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_73 ),
    inference(resolution,[],[f5719,f168])).

fof(f5719,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl12_73 ),
    inference(resolution,[],[f5718,f183])).

fof(f5718,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl12_73 ),
    inference(resolution,[],[f5683,f180])).

fof(f180,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',dt_l1_pre_topc)).

fof(f5683,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl12_73 ),
    inference(avatar_component_clause,[],[f5682])).

fof(f5682,plain,
    ( spl12_73
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_73])])).

fof(f5717,plain,(
    spl12_71 ),
    inference(avatar_contradiction_clause,[],[f5716])).

fof(f5716,plain,
    ( $false
    | ~ spl12_71 ),
    inference(subsumption_resolution,[],[f5715,f163])).

fof(f5715,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_71 ),
    inference(subsumption_resolution,[],[f5714,f164])).

fof(f5714,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_71 ),
    inference(subsumption_resolution,[],[f5713,f165])).

fof(f5713,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_71 ),
    inference(subsumption_resolution,[],[f5711,f166])).

fof(f5711,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_71 ),
    inference(resolution,[],[f5677,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t111_tmap_1.p',dt_k7_tmap_1)).

fof(f5677,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_71 ),
    inference(avatar_component_clause,[],[f5676])).

fof(f5710,plain,(
    spl12_69 ),
    inference(avatar_contradiction_clause,[],[f5709])).

fof(f5709,plain,
    ( $false
    | ~ spl12_69 ),
    inference(subsumption_resolution,[],[f5708,f163])).

fof(f5708,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_69 ),
    inference(subsumption_resolution,[],[f5707,f164])).

fof(f5707,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_69 ),
    inference(subsumption_resolution,[],[f5706,f165])).

fof(f5706,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_69 ),
    inference(subsumption_resolution,[],[f5705,f166])).

fof(f5705,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_69 ),
    inference(resolution,[],[f5671,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f5671,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_69 ),
    inference(avatar_component_clause,[],[f5670])).

fof(f5704,plain,(
    spl12_67 ),
    inference(avatar_contradiction_clause,[],[f5703])).

fof(f5703,plain,
    ( $false
    | ~ spl12_67 ),
    inference(subsumption_resolution,[],[f5702,f163])).

fof(f5702,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_67 ),
    inference(subsumption_resolution,[],[f5701,f164])).

fof(f5701,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_67 ),
    inference(subsumption_resolution,[],[f5700,f165])).

fof(f5700,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_67 ),
    inference(subsumption_resolution,[],[f5697,f166])).

fof(f5697,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_67 ),
    inference(resolution,[],[f5665,f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f5665,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ spl12_67 ),
    inference(avatar_component_clause,[],[f5664])).

fof(f5695,plain,(
    spl12_65 ),
    inference(avatar_contradiction_clause,[],[f5694])).

fof(f5694,plain,
    ( $false
    | ~ spl12_65 ),
    inference(subsumption_resolution,[],[f5693,f163])).

fof(f5693,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_65 ),
    inference(subsumption_resolution,[],[f5692,f164])).

fof(f5692,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_65 ),
    inference(subsumption_resolution,[],[f5691,f165])).

fof(f5691,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_65 ),
    inference(subsumption_resolution,[],[f5689,f166])).

fof(f5689,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_65 ),
    inference(resolution,[],[f5688,f214])).

fof(f5688,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_65 ),
    inference(resolution,[],[f5659,f180])).

fof(f5659,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_65 ),
    inference(avatar_component_clause,[],[f5658])).

fof(f5658,plain,
    ( spl12_65
  <=> ~ l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_65])])).

fof(f5687,plain,(
    spl12_63 ),
    inference(avatar_contradiction_clause,[],[f5686])).

fof(f5686,plain,
    ( $false
    | ~ spl12_63 ),
    inference(subsumption_resolution,[],[f5685,f165])).

fof(f5685,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_63 ),
    inference(resolution,[],[f5653,f180])).

fof(f5653,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_63 ),
    inference(avatar_component_clause,[],[f5652])).

fof(f5652,plain,
    ( spl12_63
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_63])])).

fof(f5684,plain,
    ( ~ spl12_63
    | ~ spl12_65
    | ~ spl12_67
    | ~ spl12_69
    | ~ spl12_71
    | ~ spl12_73
    | spl12_1 ),
    inference(avatar_split_clause,[],[f5647,f267,f5682,f5676,f5670,f5664,f5658,f5652])).

fof(f5647,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f247,f268])).

fof(f268,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f267])).

fof(f247,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f287,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | ~ spl12_5
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f170,f285,f279,f273,f267])).

fof(f170,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f140])).
%------------------------------------------------------------------------------
