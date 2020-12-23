%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1913+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Timeout 60.36s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   86 ( 438 expanded)
%              Number of leaves         :    5 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  434 (2770 expanded)
%              Number of equality atoms :   53 ( 306 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163240,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163239,f10598])).

fof(f10598,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f10597,f5391])).

fof(f5391,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f3865])).

fof(f3865,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3864])).

fof(f3864,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3834])).

fof(f3834,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v2_pralg_1(X1)
              & v1_partfun1(X1,X0)
              & v1_funct_1(X1)
              & v4_relat_1(X1,X0)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3833])).

fof(f3833,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_6)).

fof(f10597,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10596,f5397])).

fof(f5397,plain,(
    v2_pralg_1(sK1) ),
    inference(cnf_transformation,[],[f3865])).

fof(f10596,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ v2_pralg_1(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10595,f5396])).

fof(f5396,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f3865])).

fof(f10595,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10594,f5395])).

fof(f5395,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f3865])).

fof(f10594,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10593,f5394])).

fof(f5394,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f3865])).

fof(f10593,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10592,f5393])).

fof(f5393,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f3865])).

fof(f10592,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10590,f5398])).

fof(f5398,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f3865])).

fof(f10590,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(superposition,[],[f5392,f5412])).

fof(f5412,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ m1_subset_1(X2,X0)
      | k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3876])).

fof(f3876,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3875])).

fof(f3875,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3825])).

fof(f3825,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).

fof(f5392,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f3865])).

fof(f163239,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f163051,f143842])).

fof(f143842,plain,(
    k1_funct_1(sK1,sK2) = sK82(sK1,k12_pralg_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f10486,f10147])).

fof(f10147,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10135,f5398])).

fof(f10135,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f5391,f5825])).

fof(f5825,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4050])).

fof(f4050,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f4049])).

fof(f4049,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f10486,plain,(
    ! [X22] :
      ( ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10485,f10238])).

fof(f10238,plain,(
    v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10237,f5397])).

fof(f10237,plain,
    ( ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10236,f5396])).

fof(f10236,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10235,f5395])).

fof(f10235,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10164,f5393])).

fof(f10164,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f5394,f5693])).

fof(f5693,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | v1_partfun1(k12_pralg_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f3982])).

fof(f3982,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f3981])).

fof(f3981,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3081])).

fof(f3081,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_pralg_1)).

fof(f10485,plain,(
    ! [X22] :
      ( ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10484,f10234])).

fof(f10234,plain,(
    v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10233,f5397])).

fof(f10233,plain,
    ( ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10232,f5396])).

fof(f10232,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10231,f5395])).

fof(f10231,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10163,f5393])).

fof(f10163,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(resolution,[],[f5394,f5692])).

fof(f5692,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | v1_funct_1(k12_pralg_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3982])).

fof(f10484,plain,(
    ! [X22] :
      ( ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10483,f10230])).

fof(f10230,plain,(
    v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10229,f5397])).

fof(f10229,plain,
    ( ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10228,f5396])).

fof(f10228,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10227,f5395])).

fof(f10227,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f10162,f5393])).

fof(f10162,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f5394,f5691])).

fof(f5691,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | v4_relat_1(k12_pralg_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f3982])).

fof(f10483,plain,(
    ! [X22] :
      ( ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10482,f10226])).

fof(f10226,plain,(
    v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10225,f5397])).

fof(f10225,plain,
    ( ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10224,f5396])).

fof(f10224,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10223,f5395])).

fof(f10223,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f10161,f5393])).

fof(f10161,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(resolution,[],[f5394,f5690])).

fof(f5690,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | v1_relat_1(k12_pralg_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3982])).

fof(f10482,plain,(
    ! [X22] :
      ( ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10481,f5397])).

fof(f10481,plain,(
    ! [X22] :
      ( ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10480,f5396])).

fof(f10480,plain,(
    ! [X22] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10479,f5395])).

fof(f10479,plain,(
    ! [X22] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(subsumption_resolution,[],[f10184,f5393])).

fof(f10184,plain,(
    ! [X22] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X22,sK0)
      | k1_funct_1(sK1,X22) = sK82(sK1,k12_pralg_1(sK0,sK1),X22) ) ),
    inference(resolution,[],[f5394,f7921])).

fof(f7921,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = sK82(X1,k12_pralg_1(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f5664])).

fof(f5664,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = sK82(X1,X2,X3)
      | k12_pralg_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3978])).

fof(f3978,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f3977])).

fof(f3977,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3075])).

fof(f3075,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ~ ( ! [X4] :
                      ( l1_struct_0(X4)
                     => ~ ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                          & k1_funct_1(X1,X3) = X4 ) )
                  & r2_hidden(X3,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pralg_1)).

fof(f163051,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f10478,f10147])).

fof(f10478,plain,(
    ! [X21] :
      ( ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10477,f10238])).

fof(f10477,plain,(
    ! [X21] :
      ( ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10476,f10234])).

fof(f10476,plain,(
    ! [X21] :
      ( ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10475,f10230])).

fof(f10475,plain,(
    ! [X21] :
      ( ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10474,f10226])).

fof(f10474,plain,(
    ! [X21] :
      ( ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10473,f5397])).

fof(f10473,plain,(
    ! [X21] :
      ( ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10472,f5396])).

fof(f10472,plain,(
    ! [X21] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10471,f5395])).

fof(f10471,plain,(
    ! [X21] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(subsumption_resolution,[],[f10183,f5393])).

fof(f10183,plain,(
    ! [X21] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | ~ v2_pralg_1(sK1)
      | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
      | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
      | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
      | ~ v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
      | ~ r2_hidden(X21,sK0)
      | k1_funct_1(k12_pralg_1(sK0,sK1),X21) = u1_struct_0(sK82(sK1,k12_pralg_1(sK0,sK1),X21)) ) ),
    inference(resolution,[],[f5394,f7920])).

fof(f7920,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(k12_pralg_1(X0,X1),X3) = u1_struct_0(sK82(X1,k12_pralg_1(X0,X1),X3)) ) ),
    inference(equality_resolution,[],[f5665])).

fof(f5665,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X2,X3) = u1_struct_0(sK82(X1,X2,X3))
      | k12_pralg_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3978])).
%------------------------------------------------------------------------------
