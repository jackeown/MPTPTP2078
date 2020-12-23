%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t199_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 521 expanded)
%              Number of leaves         :   53 ( 211 expanded)
%              Depth                    :   12
%              Number of atoms          :  525 (1501 expanded)
%              Number of equality atoms :   10 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f831,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f97,f107,f117,f148,f161,f174,f185,f194,f201,f214,f221,f230,f261,f269,f307,f314,f374,f453,f465,f485,f555,f566,f643,f726,f738,f757,f792,f799,f806,f821,f825,f830])).

fof(f830,plain,
    ( spl6_1
    | spl6_9
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_64 ),
    inference(avatar_contradiction_clause,[],[f829])).

fof(f829,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f828,f118])).

fof(f118,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_funct_2(X0,sK1))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f82,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',fc1_funct_2)).

fof(f82,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f828,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl6_9
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f827,f791])).

fof(f791,plain,
    ( v1_funct_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f790])).

fof(f790,plain,
    ( spl6_58
  <=> v1_funct_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f827,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)))
    | v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl6_9
    | ~ spl6_54
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f826,f116])).

fof(f116,plain,
    ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_9
  <=> ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f826,plain,
    ( m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | ~ v1_funct_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)))
    | v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl6_54
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f823,f766])).

fof(f766,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f737,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t121_funct_2)).

fof(f737,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f736])).

fof(f736,plain,
    ( spl6_54
  <=> r2_hidden(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f823,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | ~ v1_funct_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)))
    | v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl6_64 ),
    inference(resolution,[],[f820,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(sK4(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',d13_funct_2)).

fof(f820,plain,
    ( v1_funct_2(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl6_64
  <=> v1_funct_2(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f825,plain,
    ( spl6_1
    | spl6_9
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_64 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f822,f766])).

fof(f822,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_58
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f118,f116,f791,f820,f69])).

fof(f821,plain,
    ( spl6_64
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f767,f736,f819])).

fof(f767,plain,
    ( v1_funct_2(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f737,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f806,plain,
    ( ~ spl6_63
    | ~ spl6_54
    | spl6_57 ),
    inference(avatar_split_clause,[],[f783,f755,f736,f804])).

fof(f804,plain,
    ( spl6_63
  <=> ~ m1_subset_1(k1_funct_2(sK0,sK1),k1_zfmisc_1(sK3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f755,plain,
    ( spl6_57
  <=> ~ m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f783,plain,
    ( ~ m1_subset_1(k1_funct_2(sK0,sK1),k1_zfmisc_1(sK3(sK0,sK1)))
    | ~ spl6_54
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f737,f756,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t4_subset)).

fof(f756,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f755])).

fof(f799,plain,
    ( ~ spl6_61
    | ~ spl6_54
    | spl6_57 ),
    inference(avatar_split_clause,[],[f780,f755,f736,f797])).

fof(f797,plain,
    ( spl6_61
  <=> ~ r2_hidden(k1_funct_2(sK0,sK1),k1_zfmisc_1(sK3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f780,plain,
    ( ~ r2_hidden(k1_funct_2(sK0,sK1),k1_zfmisc_1(sK3(sK0,sK1)))
    | ~ spl6_54
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f737,f756,f204])).

fof(f204,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X3))
      | ~ r2_hidden(X2,X4)
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t1_subset)).

fof(f792,plain,
    ( spl6_58
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f768,f736,f790])).

fof(f768,plain,
    ( v1_funct_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f737,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f757,plain,
    ( ~ spl6_57
    | spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f678,f115,f81,f755])).

fof(f678,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f122,f64,f116,f118,f377])).

fof(f377,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_funct_2(X3,X0,X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(sK4(X0,X1,X2),X3)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f376,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X4,X2)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f376,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(sK4(X0,X1,X2),X3)
      | ~ m1_funct_2(X3,X0,X1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f375,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( v1_funct_1(X4)
      | ~ m1_subset_1(X4,X2)
      | ~ m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f375,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(sK4(X0,X1,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(sK4(X0,X1,X2),X3)
      | ~ m1_funct_2(X3,X0,X1)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f69,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,X2)
      | ~ m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
    ! [X0,X1] : m1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] : m1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_funct_2(X2,X0,X1)
     => m1_funct_2(sK3(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0,X1] :
    ? [X2] : m1_funct_2(X2,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',existence_m1_funct_2)).

fof(f122,plain,(
    ! [X0,X1] : ~ v1_xboole_0(sK3(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f64,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_funct_2(X2,X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_funct_2(X2,X0,X1)
     => ~ v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',dt_m1_funct_2)).

fof(f738,plain,
    ( spl6_54
    | spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f625,f115,f81,f736])).

fof(f625,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f116,f118,f300])).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X0,X1,X2)
      | v1_xboole_0(X0)
      | r2_hidden(sK4(X1,X2,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X0,X1,X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X0)
      | r2_hidden(sK4(X1,X2,X0),X0) ) ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t2_subset)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),X2)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f726,plain,
    ( spl6_52
    | spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f297,f115,f81,f724])).

fof(f724,plain,
    ( spl6_52
  <=> m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f297,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f118,f116,f68])).

fof(f643,plain,
    ( ~ spl6_51
    | spl6_47 ),
    inference(avatar_split_clause,[],[f557,f553,f641])).

fof(f641,plain,
    ( spl6_51
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f553,plain,
    ( spl6_47
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f557,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_47 ),
    inference(unit_resulting_resolution,[],[f57,f554,f74])).

fof(f554,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f553])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',existence_m1_subset_1)).

fof(f566,plain,
    ( ~ spl6_49
    | spl6_47 ),
    inference(avatar_split_clause,[],[f558,f553,f564])).

fof(f564,plain,
    ( spl6_49
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f558,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_47 ),
    inference(unit_resulting_resolution,[],[f554,f60])).

fof(f555,plain,
    ( ~ spl6_47
    | ~ spl6_2
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f528,f366,f88,f553])).

fof(f88,plain,
    ( spl6_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f366,plain,
    ( spl6_36
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f528,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_2
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f367,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f75,f89])).

fof(f89,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t5_subset)).

fof(f367,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f366])).

fof(f485,plain,
    ( spl6_44
    | ~ spl6_2
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f398,f372,f267,f88,f483])).

fof(f483,plain,
    ( spl6_44
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f267,plain,
    ( spl6_30
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f372,plain,
    ( spl6_38
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f398,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_2
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f386,f268])).

fof(f268,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f386,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f373,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f98,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t6_boole)).

fof(f98,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f89,f56])).

fof(f373,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f372])).

fof(f465,plain,
    ( ~ spl6_43
    | ~ spl6_2
    | spl6_21
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f394,f372,f199,f88,f463])).

fof(f463,plain,
    ( spl6_43
  <=> ~ m1_subset_1(sK5,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f199,plain,
    ( spl6_21
  <=> ~ m1_subset_1(sK5,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f394,plain,
    ( ~ m1_subset_1(sK5,o_0_0_xboole_0)
    | ~ spl6_2
    | ~ spl6_21
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f386,f200])).

fof(f200,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f453,plain,
    ( ~ spl6_41
    | ~ spl6_2
    | spl6_17
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f393,f372,f183,f88,f451])).

fof(f451,plain,
    ( spl6_41
  <=> ~ m1_subset_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f183,plain,
    ( spl6_17
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f393,plain,
    ( ~ m1_subset_1(sK1,o_0_0_xboole_0)
    | ~ spl6_2
    | ~ spl6_17
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f386,f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f374,plain,
    ( spl6_36
    | spl6_38
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f272,f267,f372,f366])).

fof(f272,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_30 ),
    inference(resolution,[],[f268,f61])).

fof(f314,plain,
    ( ~ spl6_35
    | spl6_21 ),
    inference(avatar_split_clause,[],[f205,f199,f312])).

fof(f312,plain,
    ( spl6_35
  <=> ~ r2_hidden(sK5,sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f205,plain,
    ( ~ r2_hidden(sK5,sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f57,f200,f74])).

fof(f307,plain,
    ( ~ spl6_33
    | spl6_17 ),
    inference(avatar_split_clause,[],[f202,f183,f305])).

fof(f305,plain,
    ( spl6_33
  <=> ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f202,plain,
    ( ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f184,f57,f74])).

fof(f269,plain,
    ( spl6_30
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f262,f259,f267])).

fof(f259,plain,
    ( spl6_28
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f262,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_28 ),
    inference(superposition,[],[f57,f260])).

fof(f260,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl6_28
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f239,f228,f88,f259])).

fof(f228,plain,
    ( spl6_26
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f239,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f229,f100])).

fof(f229,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl6_26
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f223,f88,f228])).

fof(f223,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f57,f177,f61])).

fof(f177,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f89,f57,f75])).

fof(f221,plain,
    ( ~ spl6_25
    | spl6_21 ),
    inference(avatar_split_clause,[],[f206,f199,f219])).

fof(f219,plain,
    ( spl6_25
  <=> ~ r2_hidden(sK5,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f206,plain,
    ( ~ r2_hidden(sK5,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f200,f60])).

fof(f214,plain,
    ( ~ spl6_23
    | spl6_17 ),
    inference(avatar_split_clause,[],[f186,f183,f212])).

fof(f212,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f186,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f184,f60])).

fof(f201,plain,
    ( ~ spl6_21
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f176,f159,f88,f199])).

fof(f159,plain,
    ( spl6_12
  <=> r2_hidden(sK2(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f176,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f160,f89,f75])).

fof(f160,plain,
    ( r2_hidden(sK2(sK5),sK5)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f194,plain,
    ( ~ spl6_19
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f164,f159,f192])).

fof(f192,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK5,sK2(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f164,plain,
    ( ~ r2_hidden(sK5,sK2(sK5))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f160,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',antisymmetry_r2_hidden)).

fof(f185,plain,
    ( ~ spl6_17
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f175,f146,f88,f183])).

fof(f146,plain,
    ( spl6_10
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f175,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f147,f89,f75])).

fof(f147,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f174,plain,
    ( ~ spl6_15
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f151,f146,f172])).

fof(f172,plain,
    ( spl6_15
  <=> ~ r2_hidden(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f151,plain,
    ( ~ r2_hidden(sK1,sK2(sK1))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f147,f59])).

fof(f161,plain,
    ( spl6_12
    | spl6_5 ),
    inference(avatar_split_clause,[],[f138,f95,f159])).

fof(f95,plain,
    ( spl6_5
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f138,plain,
    ( r2_hidden(sK2(sK5),sK5)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f96,f57,f61])).

fof(f96,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f148,plain,
    ( spl6_10
    | spl6_1 ),
    inference(avatar_split_clause,[],[f136,f81,f146])).

fof(f136,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f82,f57,f61])).

fof(f117,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f54,f115])).

fof(f54,plain,(
    ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
        & ~ v1_xboole_0(X1) )
   => ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t199_funct_2)).

fof(f107,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f98,f88,f105])).

fof(f105,plain,
    ( spl6_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f97,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f76,f95])).

fof(f76,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f51])).

fof(f51,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',rc7_funct_1)).

fof(f90,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f55,f88])).

fof(f55,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',dt_o_0_0_xboole_0)).

fof(f83,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f53,f81])).

fof(f53,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
