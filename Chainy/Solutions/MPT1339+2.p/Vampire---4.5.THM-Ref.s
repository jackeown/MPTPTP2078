%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1339+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 211 expanded)
%              Number of leaves         :    9 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  185 (1549 expanded)
%              Number of equality atoms :   34 ( 235 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7831,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7830,f7376])).

fof(f7376,plain,(
    v1_relat_1(sK246) ),
    inference(resolution,[],[f5011,f5177])).

fof(f5177,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2547])).

fof(f2547,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f5011,plain,(
    m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(sK245)))) ),
    inference(cnf_transformation,[],[f3997])).

fof(f3997,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(sK245),sK246))
    & v2_funct_1(sK246)
    & k2_struct_0(sK245) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(sK245),sK246)
    & m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(sK245))))
    & v1_funct_2(sK246,u1_struct_0(sK244),u1_struct_0(sK245))
    & v1_funct_1(sK246)
    & l1_struct_0(sK245)
    & l1_struct_0(sK244) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK244,sK245,sK246])],[f2434,f3996,f3995,f3994])).

fof(f3994,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK244),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK244) ) ),
    introduced(choice_axiom,[])).

fof(f3995,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(X1),X2))
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK244),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(sK245),X2))
          & v2_funct_1(X2)
          & k2_struct_0(sK245) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(sK245),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(sK245))))
          & v1_funct_2(X2,u1_struct_0(sK244),u1_struct_0(sK245))
          & v1_funct_1(X2) )
      & l1_struct_0(sK245) ) ),
    introduced(choice_axiom,[])).

fof(f3996,plain,
    ( ? [X2] :
        ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(sK245),X2))
        & v2_funct_1(X2)
        & k2_struct_0(sK245) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(sK245),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(sK245))))
        & v1_funct_2(X2,u1_struct_0(sK244),u1_struct_0(sK245))
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(sK245),sK246))
      & v2_funct_1(sK246)
      & k2_struct_0(sK245) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(sK245),sK246)
      & m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(sK245))))
      & v1_funct_2(sK246,u1_struct_0(sK244),u1_struct_0(sK245))
      & v1_funct_1(sK246) ) ),
    introduced(choice_axiom,[])).

fof(f2434,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2433])).

fof(f2433,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2411])).

fof(f2411,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                 => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2410])).

fof(f2410,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f7830,plain,(
    ~ v1_relat_1(sK246) ),
    inference(subsumption_resolution,[],[f7829,f5009])).

fof(f5009,plain,(
    v1_funct_1(sK246) ),
    inference(cnf_transformation,[],[f3997])).

fof(f7829,plain,
    ( ~ v1_funct_1(sK246)
    | ~ v1_relat_1(sK246) ),
    inference(subsumption_resolution,[],[f7826,f5013])).

fof(f5013,plain,(
    v2_funct_1(sK246) ),
    inference(cnf_transformation,[],[f3997])).

fof(f7826,plain,
    ( ~ v2_funct_1(sK246)
    | ~ v1_funct_1(sK246)
    | ~ v1_relat_1(sK246) ),
    inference(resolution,[],[f7824,f5275])).

fof(f5275,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2614])).

fof(f2614,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2613])).

fof(f2613,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1033])).

fof(f1033,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f7824,plain,(
    ~ v2_funct_1(k2_funct_1(sK246)) ),
    inference(global_subsumption,[],[f7545,f7823])).

fof(f7823,plain,
    ( ~ v2_funct_1(k2_funct_1(sK246))
    | ~ m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),k2_relat_1(sK246)))) ),
    inference(subsumption_resolution,[],[f7822,f5111])).

fof(f5111,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2497])).

fof(f2497,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f7822,plain,
    ( ~ v2_funct_1(k2_funct_1(sK246))
    | k2_relat_1(sK246) != k2_relset_1(u1_struct_0(sK244),k2_relat_1(sK246),sK246)
    | ~ m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),k2_relat_1(sK246)))) ),
    inference(subsumption_resolution,[],[f7821,f5009])).

fof(f7821,plain,
    ( ~ v2_funct_1(k2_funct_1(sK246))
    | k2_relat_1(sK246) != k2_relset_1(u1_struct_0(sK244),k2_relat_1(sK246),sK246)
    | ~ m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),k2_relat_1(sK246))))
    | ~ v1_funct_1(sK246) ),
    inference(subsumption_resolution,[],[f7820,f7547])).

fof(f7547,plain,(
    v1_funct_2(sK246,u1_struct_0(sK244),k2_relat_1(sK246)) ),
    inference(backward_demodulation,[],[f5010,f7531])).

fof(f7531,plain,(
    u1_struct_0(sK245) = k2_relat_1(sK246) ),
    inference(subsumption_resolution,[],[f7501,f5008])).

fof(f5008,plain,(
    l1_struct_0(sK245) ),
    inference(cnf_transformation,[],[f3997])).

fof(f7501,plain,
    ( u1_struct_0(sK245) = k2_relat_1(sK246)
    | ~ l1_struct_0(sK245) ),
    inference(superposition,[],[f7484,f5133])).

fof(f5133,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2517])).

fof(f2517,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f7484,plain,(
    k2_struct_0(sK245) = k2_relat_1(sK246) ),
    inference(subsumption_resolution,[],[f7471,f5011])).

fof(f7471,plain,
    ( k2_struct_0(sK245) = k2_relat_1(sK246)
    | ~ m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),u1_struct_0(sK245)))) ),
    inference(superposition,[],[f5012,f5111])).

fof(f5012,plain,(
    k2_struct_0(sK245) = k2_relset_1(u1_struct_0(sK244),u1_struct_0(sK245),sK246) ),
    inference(cnf_transformation,[],[f3997])).

fof(f5010,plain,(
    v1_funct_2(sK246,u1_struct_0(sK244),u1_struct_0(sK245)) ),
    inference(cnf_transformation,[],[f3997])).

fof(f7820,plain,
    ( ~ v2_funct_1(k2_funct_1(sK246))
    | k2_relat_1(sK246) != k2_relset_1(u1_struct_0(sK244),k2_relat_1(sK246),sK246)
    | ~ m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),k2_relat_1(sK246))))
    | ~ v1_funct_2(sK246,u1_struct_0(sK244),k2_relat_1(sK246))
    | ~ v1_funct_1(sK246) ),
    inference(subsumption_resolution,[],[f7818,f5013])).

fof(f7818,plain,
    ( ~ v2_funct_1(k2_funct_1(sK246))
    | ~ v2_funct_1(sK246)
    | k2_relat_1(sK246) != k2_relset_1(u1_struct_0(sK244),k2_relat_1(sK246),sK246)
    | ~ m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),k2_relat_1(sK246))))
    | ~ v1_funct_2(sK246,u1_struct_0(sK244),k2_relat_1(sK246))
    | ~ v1_funct_1(sK246) ),
    inference(superposition,[],[f7546,f5015])).

fof(f5015,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2436])).

fof(f2436,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2435])).

fof(f2435,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2245])).

fof(f2245,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f7546,plain,(
    ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),k2_relat_1(sK246),sK246)) ),
    inference(backward_demodulation,[],[f5014,f7531])).

fof(f5014,plain,(
    ~ v2_funct_1(k2_tops_2(u1_struct_0(sK244),u1_struct_0(sK245),sK246)) ),
    inference(cnf_transformation,[],[f3997])).

fof(f7545,plain,(
    m1_subset_1(sK246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK244),k2_relat_1(sK246)))) ),
    inference(backward_demodulation,[],[f5011,f7531])).
%------------------------------------------------------------------------------
