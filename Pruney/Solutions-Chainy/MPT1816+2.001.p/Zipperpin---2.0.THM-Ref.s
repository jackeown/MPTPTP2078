%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EcST2XehHs

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:06 EST 2020

% Result     : Theorem 49.30s
% Output     : Refutation 49.33s
% Verified   : 
% Statistics : Number of formulae       :  643 (24850 expanded)
%              Number of leaves         :   47 (7194 expanded)
%              Depth                    :   51
%              Number of atoms          : 8090 (1681752 expanded)
%              Number of equality atoms :  133 (14839 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t132_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                          & ( r4_tsep_1 @ A @ D @ E ) )
                       => ( ( ( v1_funct_1 @ C )
                            & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ C @ A @ B )
                            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( A
                              = ( k1_tsep_1 @ A @ D @ E ) )
                            & ( r4_tsep_1 @ A @ D @ E ) )
                         => ( ( ( v1_funct_1 @ C )
                              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ C @ A @ B )
                              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                          <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                              & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X29 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k2_partfun1 @ X16 @ X17 @ X15 @ X18 )
        = ( k7_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t129_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X41 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X41 ) @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X41 ) @ X41 @ X37 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 ) @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 ) @ X38 @ X37 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( r4_tsep_1 @ X39 @ X41 @ X38 )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('38',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('39',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('55',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( r4_tsep_1 @ X39 @ X41 @ X38 )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82','83','84','85','86','87','88'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('99',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96','97','98','99','100','101','102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['54','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['114'])).

thf('116',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['46','115'])).

thf('117',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('119',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('120',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ) )).

thf('125',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v5_pre_topc @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X34 @ X35 @ X33 @ X36 ) @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130','131','132'])).

thf('134',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['123','133'])).

thf('135',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['121','134'])).

thf('136',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('137',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['123','133'])).

thf('140',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('142',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['122'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v5_pre_topc @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X34 @ X35 @ X33 @ X36 ) @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['144','154'])).

thf('156',plain,
    ( ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['143','155'])).

thf('157',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('158',plain,
    ( ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['144','154'])).

thf('161',plain,
    ( ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('163',plain,
    ( ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['46','115'])).

thf('165',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['166'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['165','167'])).

thf('169',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('171',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('172',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('173',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('174',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('175',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('176',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('177',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174','175','176','177','178','179','180'])).

thf('182',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['168','181'])).

thf('183',plain,
    ( ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['164','182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['163','183'])).

thf('185',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['122'])).

thf('186',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('188',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('199',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( ( k1_tsep_1 @ X48 @ X47 @ X47 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X47 ) @ ( u1_pre_topc @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['197','207'])).

thf('209',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['122'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v5_pre_topc @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X34 @ X35 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216','217','218'])).

thf('220',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['209','219'])).

thf('221',plain,
    ( ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['208','220'])).

thf('222',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['195','196'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('230',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('231',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('233',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('234',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('235',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['233','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('241',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_pre_topc @ X50 @ X51 )
      | ( m1_pre_topc @ X52 @ X51 )
      | ~ ( m1_pre_topc @ X52 @ X50 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['239','245'])).

thf('247',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('248',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('249',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['246','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('256',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('260',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('261',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('264',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t22_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('265',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( m1_pre_topc @ X44 @ ( k1_tsep_1 @ X45 @ X44 @ X46 ) )
      | ~ ( m1_pre_topc @ X46 @ X45 )
      | ( v2_struct_0 @ X46 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['263','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_pre_topc @ X50 @ X51 )
      | ( m1_pre_topc @ X52 @ X51 )
      | ~ ( m1_pre_topc @ X52 @ X50 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['262','271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['258','273'])).

thf('275',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['249','250'])).

thf('276',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('278',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['274','275','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['232','284'])).

thf('286',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['249','250'])).

thf('287',plain,(
    m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_D @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('289',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_pre_topc @ X50 @ X51 )
      | ( m1_pre_topc @ X52 @ X51 )
      | ~ ( m1_pre_topc @ X52 @ X50 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ( m1_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['287','291'])).

thf('293',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['249','250'])).

thf('294',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(clc,[status(thm)],['295','296'])).

thf('298',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( ( k1_tsep_1 @ X48 @ X47 @ X47 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X47 ) @ ( u1_pre_topc @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('299',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( ( k1_tsep_1 @ sk_D @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('301',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['249','250'])).

thf('302',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_D @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,
    ( ( ( k1_tsep_1 @ sk_D @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('307',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('308',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['308'])).

thf('310',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('311',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['309','312'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['313'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('315',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('318',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('319',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('323',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['316','324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) )
    | ~ ( v2_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['305','326'])).

thf('328',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('329',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['249','250'])).

thf('330',plain,
    ( ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['330','331'])).

thf('333',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['231','332'])).

thf('334',plain,
    ( ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['221','333'])).

thf('335',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('336',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('337',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['335','336'])).

thf('338',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['337','338','339','340'])).

thf('342',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['342','343'])).

thf('345',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['344','345'])).

thf('347',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['334','346'])).

thf('348',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['347','348'])).

thf('350',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['349','350'])).

thf('352',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('355',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['355','356'])).

thf('358',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['352','357'])).

thf('359',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['358'])).

thf('360',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) @ sk_A ) ),
    inference(clc,[status(thm)],['359','360'])).

thf('362',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) @ sk_A ),
    inference(clc,[status(thm)],['361','362'])).

thf('364',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( ( k1_tsep_1 @ X48 @ X47 @ X47 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X47 ) @ ( u1_pre_topc @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('366',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['366','367','368'])).

thf('370',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['369','370'])).

thf('372',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('374',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['363','373'])).

thf('375',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['209','219'])).

thf('376',plain,
    ( ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) @ sk_A ),
    inference(clc,[status(thm)],['361','362'])).

thf('378',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('379',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['377','378'])).

thf('380',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) ) ) ) ),
    inference(clc,[status(thm)],['379','380'])).

thf('382',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_E @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['381','382'])).

thf('384',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('385',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('386',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['383','384','385'])).

thf('387',plain,(
    ! [X49: $i] :
      ( ( m1_pre_topc @ X49 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('388',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('389',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('390',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_pre_topc @ X50 @ X51 )
      | ( m1_pre_topc @ X52 @ X51 )
      | ~ ( m1_pre_topc @ X52 @ X50 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('391',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_E )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['389','390'])).

thf('392',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_E )
      | ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['391','392','393'])).

thf('395',plain,
    ( ~ ( l1_pre_topc @ sk_E )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['388','394'])).

thf('396',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('398',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['396','397'])).

thf('399',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['398','399'])).

thf('401',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) @ sk_A ) ),
    inference(demod,[status(thm)],['395','400'])).

thf('402',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) @ sk_A ),
    inference(clc,[status(thm)],['401','402'])).

thf('404',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('405',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['403','404'])).

thf('406',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) ),
    inference(demod,[status(thm)],['405','406'])).

thf('408',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['272'])).

thf('409',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_E )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v2_pre_topc @ sk_E )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) )
      | ~ ( m1_pre_topc @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['398','399'])).

thf('411',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('413',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['411','412'])).

thf('414',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('415',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('416',plain,(
    v2_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['413','414','415'])).

thf('417',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) )
      | ~ ( m1_pre_topc @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['409','410','416'])).

thf('418',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_E )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['417','418'])).

thf('420',plain,
    ( ~ ( l1_pre_topc @ sk_E )
    | ( m1_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['387','419'])).

thf('421',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['398','399'])).

thf('422',plain,(
    m1_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_E @ sk_E @ sk_E ) ),
    inference(demod,[status(thm)],['420','421'])).

thf('423',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('424',plain,
    ( ~ ( l1_pre_topc @ sk_E )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v2_pre_topc @ sk_E )
    | ( m1_pre_topc @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['422','423'])).

thf('425',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['398','399'])).

thf('426',plain,(
    v2_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['413','414','415'])).

thf('427',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_E @ sk_E ) ),
    inference(demod,[status(thm)],['424','425','426'])).

thf('428',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,(
    m1_pre_topc @ sk_E @ sk_E ),
    inference(clc,[status(thm)],['427','428'])).

thf('430',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( ( k1_tsep_1 @ X48 @ X47 @ X47 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X47 ) @ ( u1_pre_topc @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('431',plain,
    ( ( v2_struct_0 @ sk_E )
    | ~ ( v2_pre_topc @ sk_E )
    | ~ ( l1_pre_topc @ sk_E )
    | ( ( k1_tsep_1 @ sk_E @ sk_E @ sk_E )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['429','430'])).

thf('432',plain,(
    v2_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['413','414','415'])).

thf('433',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['398','399'])).

thf('434',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( ( k1_tsep_1 @ sk_E @ sk_E @ sk_E )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['431','432','433'])).

thf('435',plain,
    ( ( ( k1_tsep_1 @ sk_E @ sk_E @ sk_E )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('437',plain,
    ( ( k1_tsep_1 @ sk_E @ sk_E @ sk_E )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ),
    inference(clc,[status(thm)],['435','436'])).

thf('438',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['325'])).

thf('439',plain,
    ( ( ( u1_struct_0 @ sk_E )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) )
    | ~ ( v2_pre_topc @ sk_E )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_E ) ),
    inference('sup+',[status(thm)],['437','438'])).

thf('440',plain,(
    v2_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['413','414','415'])).

thf('441',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['398','399'])).

thf('442',plain,
    ( ( ( u1_struct_0 @ sk_E )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['439','440','441'])).

thf('443',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( u1_struct_0 @ sk_E )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('445',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['386','444'])).

thf('446',plain,
    ( ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['376','445'])).

thf('447',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_E @ sk_E )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('448',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('449',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A ) ),
    inference('sup-',[status(thm)],['447','448'])).

thf('450',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('451',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('452',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['449','450','451','452'])).

thf('454',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['453'])).

thf('455',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('456',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['454','455'])).

thf('457',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('458',plain,(
    ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_E ) @ ( u1_pre_topc @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['456','457'])).

thf('459',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['446','458'])).

thf('460',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,
    ( ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['459','460'])).

thf('462',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('463',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['461','462'])).

thf('464',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['184','185','351','463'])).

thf('465',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['158','464'])).

thf('466',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['465'])).

thf('467',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','466'])).

thf('468',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['467'])).

thf('469',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','468'])).

thf('470',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['469'])).

thf('471',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('472',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['470','471'])).

thf('473',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('474',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['472','473'])).

thf('475',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['474','475'])).

thf('477',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('478',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['476','477'])).

thf('479',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['122'])).

thf('480',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('481',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('482',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X39 @ X41 @ X38 ) ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( r4_tsep_1 @ X39 @ X41 @ X38 )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('483',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['481','482'])).

thf('484',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('485',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('486',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('487',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('488',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('489',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('490',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('491',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('492',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('493',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('494',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('495',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['483','484','485','486','487','488','489','490','491','492','493','494'])).

thf('496',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['480','495'])).

thf('497',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('498',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('499',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('500',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('501',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('502',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('503',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('504',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('505',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('506',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('507',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('508',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['496','497','498','499','500','501','502','503','504','505','506','507','508'])).

thf('510',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['479','509'])).

thf('511',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('512',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('513',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['511','512'])).

thf('514',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['510','513'])).

thf('515',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('516',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['514','515'])).

thf('517',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('518',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['516','517'])).

thf('519',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('520',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['518','519'])).

thf('521',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('522',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['520','521'])).

thf('523',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('524',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['523'])).

thf('525',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['478','522','524'])).

thf('526',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['120','525'])).

thf('527',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('528',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['527'])).

thf('529',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('530',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['528','529'])).

thf('531',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('532',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['531'])).

thf('533',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['478','522','532'])).

thf('534',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['530','533'])).

thf('535',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('536',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['535'])).

thf('537',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('538',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['536','537'])).

thf('539',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['122'])).

thf('540',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['478','522','539'])).

thf('541',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['538','540'])).

thf('542',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','116','526','534','541'])).

thf('543',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','542'])).

thf('544',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['166'])).

thf('545',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('546',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['544','545'])).

thf('547',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('548',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['547'])).

thf('549',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['478','522','548'])).

thf('550',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['546','549'])).

thf('551',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('552',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('553',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('554',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['553'])).

thf('555',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('556',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['554','555'])).

thf('557',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('558',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['557'])).

thf('559',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['478','522','558'])).

thf('560',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['556','559'])).

thf('561',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('562',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('563',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['562'])).

thf('564',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('565',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['563','564'])).

thf('566',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('567',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['566'])).

thf('568',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['478','522','567'])).

thf('569',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['565','568'])).

thf('570',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('571',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('572',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['571'])).

thf('573',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('574',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['572','573'])).

thf('575',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('576',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['575'])).

thf('577',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['478','522','576'])).

thf('578',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['574','577'])).

thf('579',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('580',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('581',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('582',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('583',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['543','550','551','552','560','561','569','570','578','579','580','581','582'])).

thf('584',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('585',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['478','522'])).

thf('586',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['584','585'])).

thf('587',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['583','586'])).

thf('588',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('589',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['587','588'])).

thf('590',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('591',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['589','590'])).

thf('592',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('593',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['591','592'])).

thf('594',plain,(
    $false ),
    inference(demod,[status(thm)],['0','593'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EcST2XehHs
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 49.30/49.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 49.30/49.49  % Solved by: fo/fo7.sh
% 49.30/49.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.30/49.49  % done 10642 iterations in 49.024s
% 49.30/49.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 49.30/49.49  % SZS output start Refutation
% 49.30/49.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 49.30/49.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 49.30/49.49  thf(sk_B_type, type, sk_B: $i).
% 49.30/49.49  thf(sk_A_type, type, sk_A: $i).
% 49.30/49.49  thf(sk_E_type, type, sk_E: $i).
% 49.30/49.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 49.30/49.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 49.30/49.49  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 49.30/49.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 49.30/49.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 49.30/49.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 49.30/49.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 49.30/49.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 49.30/49.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 49.30/49.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 49.30/49.49  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 49.30/49.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 49.30/49.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 49.30/49.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 49.30/49.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 49.30/49.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 49.30/49.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 49.30/49.49  thf(sk_C_type, type, sk_C: $i).
% 49.30/49.49  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 49.30/49.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 49.30/49.49  thf(sk_D_type, type, sk_D: $i).
% 49.30/49.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 49.30/49.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 49.30/49.49  thf(t132_tmap_1, conjecture,
% 49.30/49.49    (![A:$i]:
% 49.30/49.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.30/49.49       ( ![B:$i]:
% 49.30/49.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 49.30/49.49             ( l1_pre_topc @ B ) ) =>
% 49.30/49.49           ( ![C:$i]:
% 49.30/49.49             ( ( ( v1_funct_1 @ C ) & 
% 49.30/49.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                 ( m1_subset_1 @
% 49.30/49.49                   C @ 
% 49.30/49.49                   ( k1_zfmisc_1 @
% 49.30/49.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 49.30/49.49               ( ![D:$i]:
% 49.30/49.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 49.30/49.49                   ( ![E:$i]:
% 49.30/49.49                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 49.30/49.49                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 49.30/49.49                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 49.30/49.49                         ( ( ( v1_funct_1 @ C ) & 
% 49.30/49.49                             ( v1_funct_2 @
% 49.30/49.49                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                             ( v5_pre_topc @ C @ A @ B ) & 
% 49.30/49.49                             ( m1_subset_1 @
% 49.30/49.49                               C @ 
% 49.30/49.49                               ( k1_zfmisc_1 @
% 49.30/49.49                                 ( k2_zfmisc_1 @
% 49.30/49.49                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 49.30/49.49                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 49.30/49.49                             ( v1_funct_2 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 49.30/49.49                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                             ( v5_pre_topc @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 49.30/49.49                             ( m1_subset_1 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 49.30/49.49                               ( k1_zfmisc_1 @
% 49.30/49.49                                 ( k2_zfmisc_1 @
% 49.30/49.49                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 49.30/49.49                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 49.30/49.49                             ( v1_funct_2 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 49.30/49.49                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                             ( v5_pre_topc @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 49.30/49.49                             ( m1_subset_1 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 49.30/49.49                               ( k1_zfmisc_1 @
% 49.30/49.49                                 ( k2_zfmisc_1 @
% 49.30/49.49                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 49.30/49.49  thf(zf_stmt_0, negated_conjecture,
% 49.30/49.49    (~( ![A:$i]:
% 49.30/49.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 49.30/49.49            ( l1_pre_topc @ A ) ) =>
% 49.30/49.49          ( ![B:$i]:
% 49.30/49.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 49.30/49.49                ( l1_pre_topc @ B ) ) =>
% 49.30/49.49              ( ![C:$i]:
% 49.30/49.49                ( ( ( v1_funct_1 @ C ) & 
% 49.30/49.49                    ( v1_funct_2 @
% 49.30/49.49                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                    ( m1_subset_1 @
% 49.30/49.49                      C @ 
% 49.30/49.49                      ( k1_zfmisc_1 @
% 49.30/49.49                        ( k2_zfmisc_1 @
% 49.30/49.49                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 49.30/49.49                  ( ![D:$i]:
% 49.30/49.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 49.30/49.49                      ( ![E:$i]:
% 49.30/49.49                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 49.30/49.49                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 49.30/49.49                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 49.30/49.49                            ( ( ( v1_funct_1 @ C ) & 
% 49.30/49.49                                ( v1_funct_2 @
% 49.30/49.49                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                                ( v5_pre_topc @ C @ A @ B ) & 
% 49.30/49.49                                ( m1_subset_1 @
% 49.30/49.49                                  C @ 
% 49.30/49.49                                  ( k1_zfmisc_1 @
% 49.30/49.49                                    ( k2_zfmisc_1 @
% 49.30/49.49                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 49.30/49.49                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 49.30/49.49                                ( v1_funct_2 @
% 49.30/49.49                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 49.30/49.49                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                                ( v5_pre_topc @
% 49.30/49.49                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 49.30/49.49                                ( m1_subset_1 @
% 49.30/49.49                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 49.30/49.49                                  ( k1_zfmisc_1 @
% 49.30/49.49                                    ( k2_zfmisc_1 @
% 49.30/49.49                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 49.30/49.49                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 49.30/49.49                                ( v1_funct_2 @
% 49.30/49.49                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 49.30/49.49                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                                ( v5_pre_topc @
% 49.30/49.49                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 49.30/49.49                                ( m1_subset_1 @
% 49.30/49.49                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 49.30/49.49                                  ( k1_zfmisc_1 @
% 49.30/49.49                                    ( k2_zfmisc_1 @
% 49.30/49.49                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 49.30/49.49    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 49.30/49.49  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('2', plain,
% 49.30/49.49      ((m1_subset_1 @ sk_C @ 
% 49.30/49.49        (k1_zfmisc_1 @ 
% 49.30/49.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf(d4_tmap_1, axiom,
% 49.30/49.49    (![A:$i]:
% 49.30/49.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.30/49.49       ( ![B:$i]:
% 49.30/49.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 49.30/49.49             ( l1_pre_topc @ B ) ) =>
% 49.30/49.49           ( ![C:$i]:
% 49.30/49.49             ( ( ( v1_funct_1 @ C ) & 
% 49.30/49.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                 ( m1_subset_1 @
% 49.30/49.49                   C @ 
% 49.30/49.49                   ( k1_zfmisc_1 @
% 49.30/49.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 49.30/49.49               ( ![D:$i]:
% 49.30/49.49                 ( ( m1_pre_topc @ D @ A ) =>
% 49.30/49.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 49.30/49.49                     ( k2_partfun1 @
% 49.30/49.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 49.30/49.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 49.30/49.49  thf('3', plain,
% 49.30/49.49      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 49.30/49.49         ((v2_struct_0 @ X26)
% 49.30/49.49          | ~ (v2_pre_topc @ X26)
% 49.30/49.49          | ~ (l1_pre_topc @ X26)
% 49.30/49.49          | ~ (m1_pre_topc @ X27 @ X28)
% 49.30/49.49          | ((k2_tmap_1 @ X28 @ X26 @ X29 @ X27)
% 49.30/49.49              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ 
% 49.30/49.49                 X29 @ (u1_struct_0 @ X27)))
% 49.30/49.49          | ~ (m1_subset_1 @ X29 @ 
% 49.30/49.49               (k1_zfmisc_1 @ 
% 49.30/49.49                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 49.30/49.49          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 49.30/49.49          | ~ (v1_funct_1 @ X29)
% 49.30/49.49          | ~ (l1_pre_topc @ X28)
% 49.30/49.49          | ~ (v2_pre_topc @ X28)
% 49.30/49.49          | (v2_struct_0 @ X28))),
% 49.30/49.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 49.30/49.49  thf('4', plain,
% 49.30/49.49      (![X0 : $i]:
% 49.30/49.49         ((v2_struct_0 @ sk_A)
% 49.30/49.49          | ~ (v2_pre_topc @ sk_A)
% 49.30/49.49          | ~ (l1_pre_topc @ sk_A)
% 49.30/49.49          | ~ (v1_funct_1 @ sk_C)
% 49.30/49.49          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.30/49.49          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 49.30/49.49              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 49.30/49.49                 sk_C @ (u1_struct_0 @ X0)))
% 49.30/49.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.30/49.49          | ~ (l1_pre_topc @ sk_B)
% 49.30/49.49          | ~ (v2_pre_topc @ sk_B)
% 49.30/49.49          | (v2_struct_0 @ sk_B))),
% 49.30/49.49      inference('sup-', [status(thm)], ['2', '3'])).
% 49.30/49.49  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('8', plain,
% 49.30/49.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('9', plain,
% 49.30/49.49      ((m1_subset_1 @ sk_C @ 
% 49.30/49.49        (k1_zfmisc_1 @ 
% 49.30/49.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf(redefinition_k2_partfun1, axiom,
% 49.30/49.49    (![A:$i,B:$i,C:$i,D:$i]:
% 49.30/49.49     ( ( ( v1_funct_1 @ C ) & 
% 49.30/49.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 49.30/49.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 49.30/49.49  thf('10', plain,
% 49.30/49.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 49.30/49.49         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 49.30/49.49          | ~ (v1_funct_1 @ X15)
% 49.30/49.49          | ((k2_partfun1 @ X16 @ X17 @ X15 @ X18) = (k7_relat_1 @ X15 @ X18)))),
% 49.30/49.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 49.30/49.49  thf('11', plain,
% 49.30/49.49      (![X0 : $i]:
% 49.30/49.49         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 49.30/49.49            X0) = (k7_relat_1 @ sk_C @ X0))
% 49.30/49.49          | ~ (v1_funct_1 @ sk_C))),
% 49.30/49.49      inference('sup-', [status(thm)], ['9', '10'])).
% 49.30/49.49  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('13', plain,
% 49.30/49.49      (![X0 : $i]:
% 49.30/49.49         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 49.30/49.49           X0) = (k7_relat_1 @ sk_C @ X0))),
% 49.30/49.49      inference('demod', [status(thm)], ['11', '12'])).
% 49.30/49.49  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('16', plain,
% 49.30/49.49      (![X0 : $i]:
% 49.30/49.49         ((v2_struct_0 @ sk_A)
% 49.30/49.49          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 49.30/49.49              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 49.30/49.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.30/49.49          | (v2_struct_0 @ sk_B))),
% 49.30/49.49      inference('demod', [status(thm)],
% 49.30/49.49                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 49.30/49.49  thf('17', plain,
% 49.30/49.49      (((v2_struct_0 @ sk_B)
% 49.30/49.49        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.30/49.49            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.30/49.49        | (v2_struct_0 @ sk_A))),
% 49.30/49.49      inference('sup-', [status(thm)], ['1', '16'])).
% 49.30/49.49  thf('18', plain, (~ (v2_struct_0 @ sk_B)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('19', plain,
% 49.30/49.49      (((v2_struct_0 @ sk_A)
% 49.30/49.49        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.30/49.49            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 49.30/49.49      inference('clc', [status(thm)], ['17', '18'])).
% 49.30/49.49  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('21', plain,
% 49.30/49.49      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.30/49.49         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.30/49.49      inference('clc', [status(thm)], ['19', '20'])).
% 49.30/49.49  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('23', plain,
% 49.30/49.49      (![X0 : $i]:
% 49.30/49.49         ((v2_struct_0 @ sk_A)
% 49.30/49.49          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 49.30/49.49              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 49.30/49.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.30/49.49          | (v2_struct_0 @ sk_B))),
% 49.30/49.49      inference('demod', [status(thm)],
% 49.30/49.49                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 49.30/49.49  thf('24', plain,
% 49.30/49.49      (((v2_struct_0 @ sk_B)
% 49.30/49.49        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.49            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.30/49.49        | (v2_struct_0 @ sk_A))),
% 49.30/49.49      inference('sup-', [status(thm)], ['22', '23'])).
% 49.30/49.49  thf('25', plain, (~ (v2_struct_0 @ sk_B)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('26', plain,
% 49.30/49.49      (((v2_struct_0 @ sk_A)
% 49.30/49.49        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.49            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 49.30/49.49      inference('clc', [status(thm)], ['24', '25'])).
% 49.30/49.49  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 49.30/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.49  thf('28', plain,
% 49.30/49.49      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.49         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.49      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.49  thf(t129_tmap_1, axiom,
% 49.30/49.49    (![A:$i]:
% 49.30/49.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.30/49.49       ( ![B:$i]:
% 49.30/49.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 49.30/49.49             ( l1_pre_topc @ B ) ) =>
% 49.30/49.49           ( ![C:$i]:
% 49.30/49.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.30/49.49               ( ![D:$i]:
% 49.30/49.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 49.30/49.49                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 49.30/49.49                     ( ![E:$i]:
% 49.30/49.49                       ( ( ( v1_funct_1 @ E ) & 
% 49.30/49.49                           ( v1_funct_2 @
% 49.30/49.49                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                           ( m1_subset_1 @
% 49.30/49.49                             E @ 
% 49.30/49.49                             ( k1_zfmisc_1 @
% 49.30/49.49                               ( k2_zfmisc_1 @
% 49.30/49.49                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 49.30/49.49                         ( ( ( v1_funct_1 @
% 49.30/49.49                               ( k2_tmap_1 @
% 49.30/49.49                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 49.30/49.49                             ( v1_funct_2 @
% 49.30/49.49                               ( k2_tmap_1 @
% 49.30/49.49                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 49.30/49.49                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 49.30/49.49                               ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                             ( v5_pre_topc @
% 49.30/49.49                               ( k2_tmap_1 @
% 49.30/49.49                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 49.30/49.49                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 49.30/49.49                             ( m1_subset_1 @
% 49.30/49.49                               ( k2_tmap_1 @
% 49.30/49.49                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 49.30/49.49                               ( k1_zfmisc_1 @
% 49.30/49.49                                 ( k2_zfmisc_1 @
% 49.30/49.49                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 49.30/49.49                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 49.30/49.49                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 49.30/49.49                             ( v1_funct_2 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 49.30/49.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                             ( v5_pre_topc @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 49.30/49.49                             ( m1_subset_1 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 49.30/49.49                               ( k1_zfmisc_1 @
% 49.30/49.49                                 ( k2_zfmisc_1 @
% 49.30/49.49                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 49.30/49.49                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 49.30/49.49                             ( v1_funct_2 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 49.30/49.49                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 49.30/49.49                             ( v5_pre_topc @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 49.30/49.49                             ( m1_subset_1 @
% 49.30/49.49                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 49.30/49.49                               ( k1_zfmisc_1 @
% 49.30/49.49                                 ( k2_zfmisc_1 @
% 49.30/49.49                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 49.30/49.49  thf('29', plain,
% 49.30/49.49      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 49.30/49.49         ((v2_struct_0 @ X37)
% 49.30/49.49          | ~ (v2_pre_topc @ X37)
% 49.30/49.49          | ~ (l1_pre_topc @ X37)
% 49.30/49.49          | (v2_struct_0 @ X38)
% 49.30/49.49          | ~ (m1_pre_topc @ X38 @ X39)
% 49.30/49.49          | ~ (v1_funct_1 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X41))
% 49.30/49.49          | ~ (v1_funct_2 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X41) @ 
% 49.30/49.49               (u1_struct_0 @ X41) @ (u1_struct_0 @ X37))
% 49.30/49.49          | ~ (v5_pre_topc @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X41) @ X41 @ X37)
% 49.30/49.49          | ~ (m1_subset_1 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X41) @ 
% 49.30/49.49               (k1_zfmisc_1 @ 
% 49.30/49.49                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X37))))
% 49.30/49.49          | ~ (v1_funct_1 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X38))
% 49.30/49.49          | ~ (v1_funct_2 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X38) @ 
% 49.30/49.49               (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))
% 49.30/49.49          | ~ (v5_pre_topc @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X38) @ X38 @ X37)
% 49.30/49.49          | ~ (m1_subset_1 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X38) @ 
% 49.30/49.49               (k1_zfmisc_1 @ 
% 49.30/49.49                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 49.30/49.49          | (v5_pre_topc @ 
% 49.30/49.49             (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.30/49.49             (k1_tsep_1 @ X39 @ X41 @ X38) @ X37)
% 49.30/49.49          | ~ (m1_subset_1 @ X40 @ 
% 49.30/49.49               (k1_zfmisc_1 @ 
% 49.30/49.49                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 49.30/49.49          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 49.30/49.49          | ~ (v1_funct_1 @ X40)
% 49.30/49.49          | ~ (r4_tsep_1 @ X39 @ X41 @ X38)
% 49.30/49.49          | ~ (m1_pre_topc @ X41 @ X39)
% 49.30/49.49          | (v2_struct_0 @ X41)
% 49.30/49.49          | ~ (l1_pre_topc @ X39)
% 49.30/49.49          | ~ (v2_pre_topc @ X39)
% 49.30/49.49          | (v2_struct_0 @ X39))),
% 49.30/49.49      inference('cnf', [status(esa)], [t129_tmap_1])).
% 49.30/49.49  thf('30', plain,
% 49.30/49.49      (![X0 : $i]:
% 49.30/49.49         (~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.49             (k1_zfmisc_1 @ 
% 49.30/49.49              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.49          | (v2_struct_0 @ sk_A)
% 49.30/49.49          | ~ (v2_pre_topc @ sk_A)
% 49.30/49.49          | ~ (l1_pre_topc @ sk_A)
% 49.30/49.49          | (v2_struct_0 @ sk_D)
% 49.30/49.49          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 49.30/49.49          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 49.30/49.49          | ~ (v1_funct_1 @ sk_C)
% 49.30/49.49          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.30/49.49          | ~ (m1_subset_1 @ sk_C @ 
% 49.30/49.49               (k1_zfmisc_1 @ 
% 49.30/49.49                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.30/49.49          | (v5_pre_topc @ 
% 49.30/49.49             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 49.30/49.49             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 49.30/49.49          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.30/49.49               (k1_zfmisc_1 @ 
% 49.30/49.49                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 49.30/49.49          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 49.30/49.49          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.30/49.49               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 49.30/49.49          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 49.30/49.50          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 49.30/49.50               sk_B)
% 49.30/49.50          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.30/49.50          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 49.30/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ X0)
% 49.30/49.50          | ~ (l1_pre_topc @ sk_B)
% 49.30/49.50          | ~ (v2_pre_topc @ sk_B)
% 49.30/49.50          | (v2_struct_0 @ sk_B))),
% 49.30/49.50      inference('sup-', [status(thm)], ['28', '29'])).
% 49.30/49.50  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('35', plain,
% 49.30/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('36', plain,
% 49.30/49.50      ((m1_subset_1 @ sk_C @ 
% 49.30/49.50        (k1_zfmisc_1 @ 
% 49.30/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('37', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('38', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('39', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('42', plain,
% 49.30/49.50      (![X0 : $i]:
% 49.30/49.50         (~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50          | (v2_struct_0 @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ sk_D)
% 49.30/49.50          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 49.30/49.50          | (v5_pre_topc @ 
% 49.30/49.50             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 49.30/49.50             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 49.30/49.50          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 49.30/49.50          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.30/49.50               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 49.30/49.50          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 49.30/49.50          | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50               sk_D @ sk_B)
% 49.30/49.50          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.30/49.50          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.30/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ X0)
% 49.30/49.50          | (v2_struct_0 @ sk_B))),
% 49.30/49.50      inference('demod', [status(thm)],
% 49.30/49.50                ['30', '31', '32', '33', '34', '35', '36', '37', '38', '39', 
% 49.30/49.50                 '40', '41'])).
% 49.30/49.50  thf('43', plain,
% 49.30/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50         (k1_zfmisc_1 @ 
% 49.30/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | (v1_funct_1 @ sk_C))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('44', plain,
% 49.30/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50         (k1_zfmisc_1 @ 
% 49.30/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 49.30/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.30/49.50      inference('split', [status(esa)], ['43'])).
% 49.30/49.50  thf('45', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('46', plain,
% 49.30/49.50      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50         (k1_zfmisc_1 @ 
% 49.30/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 49.30/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.30/49.50      inference('demod', [status(thm)], ['44', '45'])).
% 49.30/49.50  thf('47', plain,
% 49.30/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50         (k1_zfmisc_1 @ 
% 49.30/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('48', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('49', plain,
% 49.30/49.50      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50         (k1_zfmisc_1 @ 
% 49.30/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.30/49.50      inference('demod', [status(thm)], ['47', '48'])).
% 49.30/49.50  thf('50', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('51', plain,
% 49.30/49.50      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 49.30/49.50             sk_B)
% 49.30/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.30/49.50             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.30/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 49.30/49.50        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 49.30/49.50             sk_B)
% 49.30/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.30/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 49.30/49.50        | ~ (m1_subset_1 @ sk_C @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.30/49.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.30/49.50        | ~ (v1_funct_1 @ sk_C))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('52', plain,
% 49.30/49.50      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 49.30/49.50         <= (~
% 49.30/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.30/49.50      inference('split', [status(esa)], ['51'])).
% 49.30/49.50  thf('53', plain,
% 49.30/49.50      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 49.30/49.50         <= (~
% 49.30/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.30/49.50      inference('sup-', [status(thm)], ['50', '52'])).
% 49.30/49.50  thf('54', plain,
% 49.30/49.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.30/49.50         <= (~
% 49.30/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.30/49.50      inference('sup-', [status(thm)], ['49', '53'])).
% 49.30/49.50  thf(t2_tsep_1, axiom,
% 49.30/49.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 49.30/49.50  thf('55', plain,
% 49.30/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.30/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.30/49.50  thf('56', plain,
% 49.30/49.50      (![X0 : $i]:
% 49.30/49.50         ((v2_struct_0 @ sk_A)
% 49.30/49.50          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 49.30/49.50              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 49.30/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ sk_B))),
% 49.30/49.50      inference('demod', [status(thm)],
% 49.30/49.50                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 49.30/49.50  thf('57', plain,
% 49.30/49.50      ((~ (l1_pre_topc @ sk_A)
% 49.30/49.50        | (v2_struct_0 @ sk_B)
% 49.30/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 49.30/49.50            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 49.30/49.50        | (v2_struct_0 @ sk_A))),
% 49.30/49.50      inference('sup-', [status(thm)], ['55', '56'])).
% 49.30/49.50  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('59', plain,
% 49.30/49.50      ((m1_subset_1 @ sk_C @ 
% 49.30/49.50        (k1_zfmisc_1 @ 
% 49.30/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf(cc2_relset_1, axiom,
% 49.30/49.50    (![A:$i,B:$i,C:$i]:
% 49.30/49.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 49.30/49.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 49.30/49.50  thf('60', plain,
% 49.30/49.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 49.30/49.50         ((v4_relat_1 @ X12 @ X13)
% 49.30/49.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 49.30/49.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 49.30/49.50  thf('61', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 49.30/49.50      inference('sup-', [status(thm)], ['59', '60'])).
% 49.30/49.50  thf(t209_relat_1, axiom,
% 49.30/49.50    (![A:$i,B:$i]:
% 49.30/49.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 49.30/49.50       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 49.30/49.50  thf('62', plain,
% 49.30/49.50      (![X10 : $i, X11 : $i]:
% 49.30/49.50         (((X10) = (k7_relat_1 @ X10 @ X11))
% 49.30/49.50          | ~ (v4_relat_1 @ X10 @ X11)
% 49.30/49.50          | ~ (v1_relat_1 @ X10))),
% 49.30/49.50      inference('cnf', [status(esa)], [t209_relat_1])).
% 49.30/49.50  thf('63', plain,
% 49.30/49.50      ((~ (v1_relat_1 @ sk_C)
% 49.30/49.50        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 49.30/49.50      inference('sup-', [status(thm)], ['61', '62'])).
% 49.30/49.50  thf('64', plain,
% 49.30/49.50      ((m1_subset_1 @ sk_C @ 
% 49.30/49.50        (k1_zfmisc_1 @ 
% 49.30/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf(cc2_relat_1, axiom,
% 49.30/49.50    (![A:$i]:
% 49.30/49.50     ( ( v1_relat_1 @ A ) =>
% 49.30/49.50       ( ![B:$i]:
% 49.30/49.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 49.30/49.50  thf('65', plain,
% 49.30/49.50      (![X6 : $i, X7 : $i]:
% 49.30/49.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 49.30/49.50          | (v1_relat_1 @ X6)
% 49.30/49.50          | ~ (v1_relat_1 @ X7))),
% 49.30/49.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 49.30/49.50  thf('66', plain,
% 49.30/49.50      ((~ (v1_relat_1 @ 
% 49.30/49.50           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 49.30/49.50        | (v1_relat_1 @ sk_C))),
% 49.30/49.50      inference('sup-', [status(thm)], ['64', '65'])).
% 49.30/49.50  thf(fc6_relat_1, axiom,
% 49.30/49.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 49.30/49.50  thf('67', plain,
% 49.30/49.50      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 49.30/49.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 49.30/49.50  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 49.30/49.50      inference('demod', [status(thm)], ['66', '67'])).
% 49.30/49.50  thf('69', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 49.30/49.50      inference('demod', [status(thm)], ['63', '68'])).
% 49.30/49.50  thf('70', plain,
% 49.30/49.50      (((v2_struct_0 @ sk_B)
% 49.30/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 49.30/49.50        | (v2_struct_0 @ sk_A))),
% 49.30/49.50      inference('demod', [status(thm)], ['57', '58', '69'])).
% 49.30/49.50  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('72', plain,
% 49.30/49.50      (((v2_struct_0 @ sk_A)
% 49.30/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C)))),
% 49.30/49.50      inference('clc', [status(thm)], ['70', '71'])).
% 49.30/49.50  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('74', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.30/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.30/49.50  thf('75', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('76', plain,
% 49.30/49.50      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 49.30/49.50         ((v2_struct_0 @ X37)
% 49.30/49.50          | ~ (v2_pre_topc @ X37)
% 49.30/49.50          | ~ (l1_pre_topc @ X37)
% 49.30/49.50          | (v2_struct_0 @ X38)
% 49.30/49.50          | ~ (m1_pre_topc @ X38 @ X39)
% 49.30/49.50          | ~ (v1_funct_1 @ 
% 49.30/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)))
% 49.30/49.50          | ~ (v1_funct_2 @ 
% 49.30/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.30/49.50               (u1_struct_0 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.30/49.50               (u1_struct_0 @ X37))
% 49.30/49.50          | ~ (v5_pre_topc @ 
% 49.30/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.30/49.50               (k1_tsep_1 @ X39 @ X41 @ X38) @ X37)
% 49.30/49.50          | ~ (m1_subset_1 @ 
% 49.30/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.30/49.50                 (u1_struct_0 @ X37))))
% 49.30/49.50          | (m1_subset_1 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X41) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X37))))
% 49.30/49.50          | ~ (m1_subset_1 @ X40 @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 49.30/49.50          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 49.30/49.50          | ~ (v1_funct_1 @ X40)
% 49.30/49.50          | ~ (r4_tsep_1 @ X39 @ X41 @ X38)
% 49.30/49.50          | ~ (m1_pre_topc @ X41 @ X39)
% 49.30/49.50          | (v2_struct_0 @ X41)
% 49.30/49.50          | ~ (l1_pre_topc @ X39)
% 49.30/49.50          | ~ (v2_pre_topc @ X39)
% 49.30/49.50          | (v2_struct_0 @ X39))),
% 49.30/49.50      inference('cnf', [status(esa)], [t129_tmap_1])).
% 49.30/49.50  thf('77', plain,
% 49.30/49.50      (![X0 : $i, X1 : $i]:
% 49.30/49.50         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ 
% 49.30/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.30/49.50               (u1_struct_0 @ X0))))
% 49.30/49.50          | (v2_struct_0 @ sk_A)
% 49.30/49.50          | ~ (v2_pre_topc @ sk_A)
% 49.30/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ sk_D)
% 49.30/49.50          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 49.30/49.50          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 49.30/49.50          | ~ (v1_funct_1 @ X1)
% 49.30/49.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 49.30/49.50          | ~ (m1_subset_1 @ X1 @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 49.30/49.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 49.30/49.50          | ~ (v5_pre_topc @ 
% 49.30/49.50               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.30/49.50               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 49.30/49.50          | ~ (v1_funct_2 @ 
% 49.30/49.50               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.30/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.30/49.50               (u1_struct_0 @ X0))
% 49.30/49.50          | ~ (v1_funct_1 @ 
% 49.30/49.50               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 49.30/49.50          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ sk_E)
% 49.30/49.50          | ~ (l1_pre_topc @ X0)
% 49.30/49.50          | ~ (v2_pre_topc @ X0)
% 49.30/49.50          | (v2_struct_0 @ X0))),
% 49.30/49.50      inference('sup-', [status(thm)], ['75', '76'])).
% 49.30/49.50  thf('78', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('82', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('83', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('84', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('85', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('86', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('87', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('88', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('89', plain,
% 49.30/49.50      (![X0 : $i, X1 : $i]:
% 49.30/49.50         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 49.30/49.50          | (v2_struct_0 @ sk_A)
% 49.30/49.50          | (v2_struct_0 @ sk_D)
% 49.30/49.50          | ~ (v1_funct_1 @ X1)
% 49.30/49.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 49.30/49.50          | ~ (m1_subset_1 @ X1 @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 49.30/49.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 49.30/49.50          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 49.30/49.50          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 49.30/49.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 49.30/49.50          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 49.30/49.50          | (v2_struct_0 @ sk_E)
% 49.30/49.50          | ~ (l1_pre_topc @ X0)
% 49.30/49.50          | ~ (v2_pre_topc @ X0)
% 49.30/49.50          | (v2_struct_0 @ X0))),
% 49.30/49.50      inference('demod', [status(thm)],
% 49.30/49.50                ['77', '78', '79', '80', '81', '82', '83', '84', '85', '86', 
% 49.30/49.50                 '87', '88'])).
% 49.30/49.50  thf('90', plain,
% 49.30/49.50      ((~ (m1_subset_1 @ sk_C @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | (v2_struct_0 @ sk_B)
% 49.30/49.50        | ~ (v2_pre_topc @ sk_B)
% 49.30/49.50        | ~ (l1_pre_topc @ sk_B)
% 49.30/49.50        | (v2_struct_0 @ sk_E)
% 49.30/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 49.30/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 49.30/49.50             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.30/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 49.30/49.50             sk_B)
% 49.30/49.50        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | ~ (m1_subset_1 @ sk_C @ 
% 49.30/49.50             (k1_zfmisc_1 @ 
% 49.30/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.30/49.50        | ~ (v1_funct_1 @ sk_C)
% 49.30/49.50        | (v2_struct_0 @ sk_D)
% 49.30/49.50        | (v2_struct_0 @ sk_A))),
% 49.30/49.50      inference('sup-', [status(thm)], ['74', '89'])).
% 49.30/49.50  thf('91', plain,
% 49.30/49.50      ((m1_subset_1 @ sk_C @ 
% 49.30/49.50        (k1_zfmisc_1 @ 
% 49.30/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('92', plain, ((v2_pre_topc @ sk_B)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('94', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.30/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.30/49.50  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('96', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.30/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.30/49.50  thf('97', plain,
% 49.30/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('98', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.30/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.30/49.50  thf('99', plain,
% 49.30/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.30/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.30/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.30/49.50  thf('100', plain,
% 49.30/49.50      ((m1_subset_1 @ sk_C @ 
% 49.30/49.50        (k1_zfmisc_1 @ 
% 49.30/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('101', plain,
% 49.30/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 49.30/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.30/49.50  thf('103', plain,
% 49.30/49.50      (((v2_struct_0 @ sk_B)
% 49.30/49.50        | (v2_struct_0 @ sk_E)
% 49.30/49.50        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.30/49.50        | (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50        | (v2_struct_0 @ sk_D)
% 49.30/49.50        | (v2_struct_0 @ sk_A))),
% 49.30/49.50      inference('demod', [status(thm)],
% 49.30/49.50                ['90', '91', '92', '93', '94', '95', '96', '97', '98', '99', 
% 49.30/49.50                 '100', '101', '102'])).
% 49.30/49.50  thf('104', plain,
% 49.30/49.50      ((((v2_struct_0 @ sk_A)
% 49.30/49.50         | (v2_struct_0 @ sk_D)
% 49.30/49.50         | (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50            (k1_zfmisc_1 @ 
% 49.30/49.50             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.30/49.50         | (v2_struct_0 @ sk_E)
% 49.30/49.50         | (v2_struct_0 @ sk_B)))
% 49.30/49.50         <= (~
% 49.30/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.30/49.50               (k1_zfmisc_1 @ 
% 49.30/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.30/49.50      inference('sup-', [status(thm)], ['54', '103'])).
% 49.30/49.50  thf('105', plain,
% 49.30/49.50      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.30/49.50           (k1_zfmisc_1 @ 
% 49.30/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 49.30/49.50         <= (~
% 49.30/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['50', '52'])).
% 49.33/49.50  thf('106', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['104', '105'])).
% 49.33/49.50  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('108', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['106', '107'])).
% 49.33/49.50  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('110', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('clc', [status(thm)], ['108', '109'])).
% 49.33/49.50  thf('111', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('112', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('clc', [status(thm)], ['110', '111'])).
% 49.33/49.50  thf('113', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('114', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['112', '113'])).
% 49.33/49.50  thf('115', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['114'])).
% 49.33/49.50  thf('116', plain,
% 49.33/49.50      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['46', '115'])).
% 49.33/49.50  thf('117', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('118', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 49.33/49.50               sk_B)))),
% 49.33/49.50      inference('split', [status(esa)], ['117'])).
% 49.33/49.50  thf('119', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('120', plain,
% 49.33/49.50      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 49.33/49.50               sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['118', '119'])).
% 49.33/49.50  thf('121', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('122', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 49.33/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('123', plain,
% 49.33/49.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('split', [status(esa)], ['122'])).
% 49.33/49.50  thf('124', plain,
% 49.33/49.50      ((m1_subset_1 @ sk_C @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf(fc2_tmap_1, axiom,
% 49.33/49.50    (![A:$i,B:$i,C:$i,D:$i]:
% 49.33/49.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 49.33/49.50         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 49.33/49.50         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( v1_funct_1 @ C ) & 
% 49.33/49.50         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 49.33/49.50         ( v5_pre_topc @ C @ A @ B ) & 
% 49.33/49.50         ( m1_subset_1 @
% 49.33/49.50           C @ 
% 49.33/49.50           ( k1_zfmisc_1 @
% 49.33/49.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 49.33/49.50         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 49.33/49.50       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 49.33/49.50         ( v1_funct_2 @
% 49.33/49.50           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 49.33/49.50           ( u1_struct_0 @ B ) ) & 
% 49.33/49.50         ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ))).
% 49.33/49.50  thf('125', plain,
% 49.33/49.50      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 49.33/49.50         (~ (m1_subset_1 @ X33 @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))))
% 49.33/49.50          | ~ (v5_pre_topc @ X33 @ X34 @ X35)
% 49.33/49.50          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))
% 49.33/49.50          | ~ (v1_funct_1 @ X33)
% 49.33/49.50          | ~ (l1_pre_topc @ X35)
% 49.33/49.50          | ~ (v2_pre_topc @ X35)
% 49.33/49.50          | (v2_struct_0 @ X35)
% 49.33/49.50          | ~ (l1_pre_topc @ X34)
% 49.33/49.50          | ~ (v2_pre_topc @ X34)
% 49.33/49.50          | (v2_struct_0 @ X34)
% 49.33/49.50          | (v2_struct_0 @ X36)
% 49.33/49.50          | ~ (m1_pre_topc @ X36 @ X34)
% 49.33/49.50          | (v5_pre_topc @ (k2_tmap_1 @ X34 @ X35 @ X33 @ X36) @ X36 @ X35))),
% 49.33/49.50      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 49.33/49.50  thf('126', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_B)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_B)
% 49.33/49.50          | ~ (v1_funct_1 @ sk_C)
% 49.33/49.50          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.33/49.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('sup-', [status(thm)], ['124', '125'])).
% 49.33/49.50  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('129', plain, ((v2_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('132', plain,
% 49.33/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('133', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B)
% 49.33/49.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['126', '127', '128', '129', '130', '131', '132'])).
% 49.33/49.50  thf('134', plain,
% 49.33/49.50      ((![X0 : $i]:
% 49.33/49.50          ((v2_struct_0 @ sk_B)
% 49.33/49.50           | (v2_struct_0 @ sk_A)
% 49.33/49.50           | (v2_struct_0 @ X0)
% 49.33/49.50           | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['123', '133'])).
% 49.33/49.50  thf('135', plain,
% 49.33/49.50      ((((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['121', '134'])).
% 49.33/49.50  thf('136', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('137', plain,
% 49.33/49.50      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 49.33/49.50          sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['135', '136'])).
% 49.33/49.50  thf('138', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('139', plain,
% 49.33/49.50      ((![X0 : $i]:
% 49.33/49.50          ((v2_struct_0 @ sk_B)
% 49.33/49.50           | (v2_struct_0 @ sk_A)
% 49.33/49.50           | (v2_struct_0 @ X0)
% 49.33/49.50           | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['123', '133'])).
% 49.33/49.50  thf('140', plain,
% 49.33/49.50      ((((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['138', '139'])).
% 49.33/49.50  thf('141', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('142', plain,
% 49.33/49.50      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 49.33/49.50          sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['140', '141'])).
% 49.33/49.50  thf('143', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('144', plain,
% 49.33/49.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('split', [status(esa)], ['122'])).
% 49.33/49.50  thf('145', plain,
% 49.33/49.50      ((m1_subset_1 @ sk_C @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('146', plain,
% 49.33/49.50      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 49.33/49.50         (~ (m1_subset_1 @ X33 @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))))
% 49.33/49.50          | ~ (v5_pre_topc @ X33 @ X34 @ X35)
% 49.33/49.50          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))
% 49.33/49.50          | ~ (v1_funct_1 @ X33)
% 49.33/49.50          | ~ (l1_pre_topc @ X35)
% 49.33/49.50          | ~ (v2_pre_topc @ X35)
% 49.33/49.50          | (v2_struct_0 @ X35)
% 49.33/49.50          | ~ (l1_pre_topc @ X34)
% 49.33/49.50          | ~ (v2_pre_topc @ X34)
% 49.33/49.50          | (v2_struct_0 @ X34)
% 49.33/49.50          | (v2_struct_0 @ X36)
% 49.33/49.50          | ~ (m1_pre_topc @ X36 @ X34)
% 49.33/49.50          | (v1_funct_2 @ (k2_tmap_1 @ X34 @ X35 @ X33 @ X36) @ 
% 49.33/49.50             (u1_struct_0 @ X36) @ (u1_struct_0 @ X35)))),
% 49.33/49.50      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 49.33/49.50  thf('147', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.33/49.50           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_B)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_B)
% 49.33/49.50          | ~ (v1_funct_1 @ sk_C)
% 49.33/49.50          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.33/49.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('sup-', [status(thm)], ['145', '146'])).
% 49.33/49.50  thf('148', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('153', plain,
% 49.33/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('154', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.33/49.50           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B)
% 49.33/49.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['147', '148', '149', '150', '151', '152', '153'])).
% 49.33/49.50  thf('155', plain,
% 49.33/49.50      ((![X0 : $i]:
% 49.33/49.50          ((v2_struct_0 @ sk_B)
% 49.33/49.50           | (v2_struct_0 @ sk_A)
% 49.33/49.50           | (v2_struct_0 @ X0)
% 49.33/49.50           | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50           | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.33/49.50              (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['144', '154'])).
% 49.33/49.50  thf('156', plain,
% 49.33/49.50      ((((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50          (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['143', '155'])).
% 49.33/49.50  thf('157', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('158', plain,
% 49.33/49.50      ((((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50          (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['156', '157'])).
% 49.33/49.50  thf('159', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('160', plain,
% 49.33/49.50      ((![X0 : $i]:
% 49.33/49.50          ((v2_struct_0 @ sk_B)
% 49.33/49.50           | (v2_struct_0 @ sk_A)
% 49.33/49.50           | (v2_struct_0 @ X0)
% 49.33/49.50           | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50           | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.33/49.50              (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['144', '154'])).
% 49.33/49.50  thf('161', plain,
% 49.33/49.50      ((((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50          (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['159', '160'])).
% 49.33/49.50  thf('162', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('163', plain,
% 49.33/49.50      ((((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50          (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['161', '162'])).
% 49.33/49.50  thf('164', plain,
% 49.33/49.50      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['46', '115'])).
% 49.33/49.50  thf('165', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('166', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('167', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 49.33/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('split', [status(esa)], ['166'])).
% 49.33/49.50  thf('168', plain,
% 49.33/49.50      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 49.33/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup+', [status(thm)], ['165', '167'])).
% 49.33/49.50  thf('169', plain,
% 49.33/49.50      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 49.33/49.50             sk_B)
% 49.33/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 49.33/49.50        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 49.33/49.50             sk_B)
% 49.33/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 49.33/49.50        | ~ (m1_subset_1 @ sk_C @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.33/49.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('170', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('171', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('172', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('173', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('174', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('175', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('176', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('177', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('178', plain,
% 49.33/49.50      ((m1_subset_1 @ sk_C @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('179', plain,
% 49.33/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('181', plain,
% 49.33/49.50      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 49.33/49.50             sk_B)
% 49.33/49.50        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.33/49.50        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 49.33/49.50             sk_B)
% 49.33/49.50        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.33/49.50        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['169', '170', '171', '172', '173', '174', '175', '176', 
% 49.33/49.50                 '177', '178', '179', '180'])).
% 49.33/49.50  thf('182', plain,
% 49.33/49.50      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.33/49.50         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.33/49.50         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              sk_D @ sk_B)
% 49.33/49.50         | ~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              (k1_zfmisc_1 @ 
% 49.33/49.50               (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.33/49.50         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)))
% 49.33/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['168', '181'])).
% 49.33/49.50  thf('183', plain,
% 49.33/49.50      (((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 49.33/49.50            sk_B)
% 49.33/49.50         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              sk_D @ sk_B)
% 49.33/49.50         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.33/49.50         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 49.33/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['164', '182'])).
% 49.33/49.50  thf('184', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.33/49.50         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.33/49.50         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              sk_D @ sk_B)
% 49.33/49.50         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['163', '183'])).
% 49.33/49.50  thf('185', plain,
% 49.33/49.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('split', [status(esa)], ['122'])).
% 49.33/49.50  thf('186', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('187', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf(dt_k1_tsep_1, axiom,
% 49.33/49.50    (![A:$i,B:$i,C:$i]:
% 49.33/49.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 49.33/49.50         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 49.33/49.50         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.33/49.50       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 49.33/49.50         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 49.33/49.50         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 49.33/49.50  thf('188', plain,
% 49.33/49.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X30 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X30)
% 49.33/49.50          | ~ (l1_pre_topc @ X31)
% 49.33/49.50          | (v2_struct_0 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X32)
% 49.33/49.50          | ~ (m1_pre_topc @ X32 @ X31)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X31 @ X30 @ X32) @ X31))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.33/49.50  thf('189', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['187', '188'])).
% 49.33/49.50  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('191', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['189', '190'])).
% 49.33/49.50  thf('192', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['186', '191'])).
% 49.33/49.50  thf('193', plain,
% 49.33/49.50      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('simplify', [status(thm)], ['192'])).
% 49.33/49.50  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('195', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A))),
% 49.33/49.50      inference('clc', [status(thm)], ['193', '194'])).
% 49.33/49.50  thf('196', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('197', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)),
% 49.33/49.50      inference('clc', [status(thm)], ['195', '196'])).
% 49.33/49.50  thf('198', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf(t25_tmap_1, axiom,
% 49.33/49.50    (![A:$i]:
% 49.33/49.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.33/49.50       ( ![B:$i]:
% 49.33/49.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.33/49.50           ( ( k1_tsep_1 @ A @ B @ B ) =
% 49.33/49.50             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 49.33/49.50  thf('199', plain,
% 49.33/49.50      (![X47 : $i, X48 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X47)
% 49.33/49.50          | ~ (m1_pre_topc @ X47 @ X48)
% 49.33/49.50          | ((k1_tsep_1 @ X48 @ X47 @ X47)
% 49.33/49.50              = (g1_pre_topc @ (u1_struct_0 @ X47) @ (u1_pre_topc @ X47)))
% 49.33/49.50          | ~ (l1_pre_topc @ X48)
% 49.33/49.50          | ~ (v2_pre_topc @ X48)
% 49.33/49.50          | (v2_struct_0 @ X48))),
% 49.33/49.50      inference('cnf', [status(esa)], [t25_tmap_1])).
% 49.33/49.50  thf('200', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_A)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['198', '199'])).
% 49.33/49.50  thf('201', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('203', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['200', '201', '202'])).
% 49.33/49.50  thf('204', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('205', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D)
% 49.33/49.50        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 49.33/49.50      inference('clc', [status(thm)], ['203', '204'])).
% 49.33/49.50  thf('206', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('207', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['205', '206'])).
% 49.33/49.50  thf('208', plain,
% 49.33/49.50      ((m1_pre_topc @ 
% 49.33/49.50        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_A)),
% 49.33/49.50      inference('demod', [status(thm)], ['197', '207'])).
% 49.33/49.50  thf('209', plain,
% 49.33/49.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('split', [status(esa)], ['122'])).
% 49.33/49.50  thf('210', plain,
% 49.33/49.50      ((m1_subset_1 @ sk_C @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('211', plain,
% 49.33/49.50      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 49.33/49.50         (~ (m1_subset_1 @ X33 @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))))
% 49.33/49.50          | ~ (v5_pre_topc @ X33 @ X34 @ X35)
% 49.33/49.50          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))
% 49.33/49.50          | ~ (v1_funct_1 @ X33)
% 49.33/49.50          | ~ (l1_pre_topc @ X35)
% 49.33/49.50          | ~ (v2_pre_topc @ X35)
% 49.33/49.50          | (v2_struct_0 @ X35)
% 49.33/49.50          | ~ (l1_pre_topc @ X34)
% 49.33/49.50          | ~ (v2_pre_topc @ X34)
% 49.33/49.50          | (v2_struct_0 @ X34)
% 49.33/49.50          | (v2_struct_0 @ X36)
% 49.33/49.50          | ~ (m1_pre_topc @ X36 @ X34)
% 49.33/49.50          | (v1_funct_1 @ (k2_tmap_1 @ X34 @ X35 @ X33 @ X36)))),
% 49.33/49.50      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 49.33/49.50  thf('212', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_B)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_B)
% 49.33/49.50          | ~ (v1_funct_1 @ sk_C)
% 49.33/49.50          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.33/49.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('sup-', [status(thm)], ['210', '211'])).
% 49.33/49.50  thf('213', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('215', plain, ((v2_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('216', plain, ((l1_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('218', plain,
% 49.33/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('219', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B)
% 49.33/49.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['212', '213', '214', '215', '216', '217', '218'])).
% 49.33/49.50  thf('220', plain,
% 49.33/49.50      ((![X0 : $i]:
% 49.33/49.50          ((v2_struct_0 @ sk_B)
% 49.33/49.50           | (v2_struct_0 @ sk_A)
% 49.33/49.50           | (v2_struct_0 @ X0)
% 49.33/49.50           | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50           | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['209', '219'])).
% 49.33/49.50  thf('221', plain,
% 49.33/49.50      ((((v1_funct_1 @ 
% 49.33/49.50          (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))
% 49.33/49.50         | (v2_struct_0 @ 
% 49.33/49.50            (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['208', '220'])).
% 49.33/49.50  thf('222', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)),
% 49.33/49.50      inference('clc', [status(thm)], ['195', '196'])).
% 49.33/49.50  thf('223', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ sk_A)
% 49.33/49.50          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 49.33/49.50              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 49.33/49.50  thf('224', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_B)
% 49.33/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 49.33/49.50            = (k7_relat_1 @ sk_C @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))))
% 49.33/49.50        | (v2_struct_0 @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['222', '223'])).
% 49.33/49.50  thf('225', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('226', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 49.33/49.50            = (k7_relat_1 @ sk_C @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))))),
% 49.33/49.50      inference('clc', [status(thm)], ['224', '225'])).
% 49.33/49.50  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('228', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 49.33/49.50         = (k7_relat_1 @ sk_C @ 
% 49.33/49.50            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))))),
% 49.33/49.50      inference('clc', [status(thm)], ['226', '227'])).
% 49.33/49.50  thf('229', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['205', '206'])).
% 49.33/49.50  thf('230', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['205', '206'])).
% 49.33/49.50  thf('231', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 49.33/49.50         (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50         = (k7_relat_1 @ sk_C @ 
% 49.33/49.50            (u1_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))))),
% 49.33/49.50      inference('demod', [status(thm)], ['228', '229', '230'])).
% 49.33/49.50  thf('232', plain,
% 49.33/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.33/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.33/49.50  thf('233', plain,
% 49.33/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.33/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.33/49.50  thf('234', plain,
% 49.33/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.33/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.33/49.50  thf('235', plain,
% 49.33/49.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X30 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X30)
% 49.33/49.50          | ~ (l1_pre_topc @ X31)
% 49.33/49.50          | (v2_struct_0 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X32)
% 49.33/49.50          | ~ (m1_pre_topc @ X32 @ X31)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X31 @ X30 @ X32) @ X31))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.33/49.50  thf('236', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X1) @ X0)
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (v2_struct_0 @ X1)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['234', '235'])).
% 49.33/49.50  thf('237', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ X1)
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X1) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['236'])).
% 49.33/49.50  thf('238', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['233', '237'])).
% 49.33/49.50  thf('239', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['238'])).
% 49.33/49.50  thf('240', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf(t7_tsep_1, axiom,
% 49.33/49.50    (![A:$i]:
% 49.33/49.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.33/49.50       ( ![B:$i]:
% 49.33/49.50         ( ( m1_pre_topc @ B @ A ) =>
% 49.33/49.50           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 49.33/49.50  thf('241', plain,
% 49.33/49.50      (![X50 : $i, X51 : $i, X52 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X50 @ X51)
% 49.33/49.50          | (m1_pre_topc @ X52 @ X51)
% 49.33/49.50          | ~ (m1_pre_topc @ X52 @ X50)
% 49.33/49.50          | ~ (l1_pre_topc @ X51)
% 49.33/49.50          | ~ (v2_pre_topc @ X51))),
% 49.33/49.50      inference('cnf', [status(esa)], [t7_tsep_1])).
% 49.33/49.50  thf('242', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (v2_pre_topc @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 49.33/49.50          | (m1_pre_topc @ X0 @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['240', '241'])).
% 49.33/49.50  thf('243', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('244', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('245', plain,
% 49.33/49.50      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_A))),
% 49.33/49.50      inference('demod', [status(thm)], ['242', '243', '244'])).
% 49.33/49.50  thf('246', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D) @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['239', '245'])).
% 49.33/49.50  thf('247', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf(dt_m1_pre_topc, axiom,
% 49.33/49.50    (![A:$i]:
% 49.33/49.50     ( ( l1_pre_topc @ A ) =>
% 49.33/49.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 49.33/49.50  thf('248', plain,
% 49.33/49.50      (![X21 : $i, X22 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X21 @ X22)
% 49.33/49.50          | (l1_pre_topc @ X21)
% 49.33/49.50          | ~ (l1_pre_topc @ X22))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.33/49.50  thf('249', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['247', '248'])).
% 49.33/49.50  thf('250', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('251', plain, ((l1_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['249', '250'])).
% 49.33/49.50  thf('252', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D) @ sk_A))),
% 49.33/49.50      inference('demod', [status(thm)], ['246', '251'])).
% 49.33/49.50  thf('253', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('254', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D) @ sk_A)),
% 49.33/49.50      inference('clc', [status(thm)], ['252', '253'])).
% 49.33/49.50  thf('255', plain,
% 49.33/49.50      (![X21 : $i, X22 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X21 @ X22)
% 49.33/49.50          | (l1_pre_topc @ X21)
% 49.33/49.50          | ~ (l1_pre_topc @ X22))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.33/49.50  thf('256', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_A)
% 49.33/49.50        | (l1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['254', '255'])).
% 49.33/49.50  thf('257', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('258', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['256', '257'])).
% 49.33/49.50  thf('259', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['238'])).
% 49.33/49.50  thf(cc1_pre_topc, axiom,
% 49.33/49.50    (![A:$i]:
% 49.33/49.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.33/49.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 49.33/49.50  thf('260', plain,
% 49.33/49.50      (![X19 : $i, X20 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X19 @ X20)
% 49.33/49.50          | (v2_pre_topc @ X19)
% 49.33/49.50          | ~ (l1_pre_topc @ X20)
% 49.33/49.50          | ~ (v2_pre_topc @ X20))),
% 49.33/49.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 49.33/49.50  thf('261', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['259', '260'])).
% 49.33/49.50  thf('262', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['261'])).
% 49.33/49.50  thf('263', plain,
% 49.33/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.33/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.33/49.50  thf('264', plain,
% 49.33/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.33/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.33/49.50  thf(t22_tsep_1, axiom,
% 49.33/49.50    (![A:$i]:
% 49.33/49.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.33/49.50       ( ![B:$i]:
% 49.33/49.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.33/49.50           ( ![C:$i]:
% 49.33/49.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.33/49.50               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 49.33/49.50  thf('265', plain,
% 49.33/49.50      (![X44 : $i, X45 : $i, X46 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X44)
% 49.33/49.50          | ~ (m1_pre_topc @ X44 @ X45)
% 49.33/49.50          | (m1_pre_topc @ X44 @ (k1_tsep_1 @ X45 @ X44 @ X46))
% 49.33/49.50          | ~ (m1_pre_topc @ X46 @ X45)
% 49.33/49.50          | (v2_struct_0 @ X46)
% 49.33/49.50          | ~ (l1_pre_topc @ X45)
% 49.33/49.50          | ~ (v2_pre_topc @ X45)
% 49.33/49.50          | (v2_struct_0 @ X45))),
% 49.33/49.50      inference('cnf', [status(esa)], [t22_tsep_1])).
% 49.33/49.50  thf('266', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X1)
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X1))
% 49.33/49.50          | (v2_struct_0 @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['264', '265'])).
% 49.33/49.50  thf('267', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         ((m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X1))
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (v2_struct_0 @ X1)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['266'])).
% 49.33/49.50  thf('268', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['263', '267'])).
% 49.33/49.50  thf('269', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['268'])).
% 49.33/49.50  thf('270', plain,
% 49.33/49.50      (![X50 : $i, X51 : $i, X52 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X50 @ X51)
% 49.33/49.50          | (m1_pre_topc @ X52 @ X51)
% 49.33/49.50          | ~ (m1_pre_topc @ X52 @ X50)
% 49.33/49.50          | ~ (l1_pre_topc @ X51)
% 49.33/49.50          | ~ (v2_pre_topc @ X51))),
% 49.33/49.50      inference('cnf', [status(esa)], [t7_tsep_1])).
% 49.33/49.50  thf('271', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['269', '270'])).
% 49.33/49.50  thf('272', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['262', '271'])).
% 49.33/49.50  thf('273', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['272'])).
% 49.33/49.50  thf('274', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ sk_D)
% 49.33/49.50          | (v2_struct_0 @ sk_D)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_D)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['258', '273'])).
% 49.33/49.50  thf('275', plain, ((l1_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['249', '250'])).
% 49.33/49.50  thf('276', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('277', plain,
% 49.33/49.50      (![X19 : $i, X20 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X19 @ X20)
% 49.33/49.50          | (v2_pre_topc @ X19)
% 49.33/49.50          | ~ (l1_pre_topc @ X20)
% 49.33/49.50          | ~ (v2_pre_topc @ X20))),
% 49.33/49.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 49.33/49.50  thf('278', plain,
% 49.33/49.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['276', '277'])).
% 49.33/49.50  thf('279', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('280', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('281', plain, ((v2_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['278', '279', '280'])).
% 49.33/49.50  thf('282', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ sk_D)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['274', '275', '281'])).
% 49.33/49.50  thf('283', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('284', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X0 @ sk_D)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['282', '283'])).
% 49.33/49.50  thf('285', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_D)
% 49.33/49.50        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['232', '284'])).
% 49.33/49.50  thf('286', plain, ((l1_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['249', '250'])).
% 49.33/49.50  thf('287', plain, ((m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_D @ sk_D @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['285', '286'])).
% 49.33/49.50  thf('288', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['238'])).
% 49.33/49.50  thf('289', plain,
% 49.33/49.50      (![X50 : $i, X51 : $i, X52 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X50 @ X51)
% 49.33/49.50          | (m1_pre_topc @ X52 @ X51)
% 49.33/49.50          | ~ (m1_pre_topc @ X52 @ X50)
% 49.33/49.50          | ~ (l1_pre_topc @ X51)
% 49.33/49.50          | ~ (v2_pre_topc @ X51))),
% 49.33/49.50      inference('cnf', [status(esa)], [t7_tsep_1])).
% 49.33/49.50  thf('290', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | (m1_pre_topc @ X1 @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['288', '289'])).
% 49.33/49.50  thf('291', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         ((m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['290'])).
% 49.33/49.50  thf('292', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_D)
% 49.33/49.50        | (m1_pre_topc @ sk_D @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['287', '291'])).
% 49.33/49.50  thf('293', plain, ((l1_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['249', '250'])).
% 49.33/49.50  thf('294', plain, ((v2_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['278', '279', '280'])).
% 49.33/49.50  thf('295', plain, (((v2_struct_0 @ sk_D) | (m1_pre_topc @ sk_D @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['292', '293', '294'])).
% 49.33/49.50  thf('296', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('297', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 49.33/49.50      inference('clc', [status(thm)], ['295', '296'])).
% 49.33/49.50  thf('298', plain,
% 49.33/49.50      (![X47 : $i, X48 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X47)
% 49.33/49.50          | ~ (m1_pre_topc @ X47 @ X48)
% 49.33/49.50          | ((k1_tsep_1 @ X48 @ X47 @ X47)
% 49.33/49.50              = (g1_pre_topc @ (u1_struct_0 @ X47) @ (u1_pre_topc @ X47)))
% 49.33/49.50          | ~ (l1_pre_topc @ X48)
% 49.33/49.50          | ~ (v2_pre_topc @ X48)
% 49.33/49.50          | (v2_struct_0 @ X48))),
% 49.33/49.50      inference('cnf', [status(esa)], [t25_tmap_1])).
% 49.33/49.50  thf('299', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_D)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_D)
% 49.33/49.50        | ((k1_tsep_1 @ sk_D @ sk_D @ sk_D)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('sup-', [status(thm)], ['297', '298'])).
% 49.33/49.50  thf('300', plain, ((v2_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['278', '279', '280'])).
% 49.33/49.50  thf('301', plain, ((l1_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['249', '250'])).
% 49.33/49.50  thf('302', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D)
% 49.33/49.50        | ((k1_tsep_1 @ sk_D @ sk_D @ sk_D)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['299', '300', '301'])).
% 49.33/49.50  thf('303', plain,
% 49.33/49.50      ((((k1_tsep_1 @ sk_D @ sk_D @ sk_D)
% 49.33/49.50          = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('simplify', [status(thm)], ['302'])).
% 49.33/49.50  thf('304', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('305', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_D @ sk_D @ sk_D)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['303', '304'])).
% 49.33/49.50  thf('306', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['238'])).
% 49.33/49.50  thf('307', plain,
% 49.33/49.50      (![X21 : $i, X22 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X21 @ X22)
% 49.33/49.50          | (l1_pre_topc @ X21)
% 49.33/49.50          | ~ (l1_pre_topc @ X22))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.33/49.50  thf('308', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['306', '307'])).
% 49.33/49.50  thf('309', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['308'])).
% 49.33/49.50  thf('310', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['268'])).
% 49.33/49.50  thf(t1_tsep_1, axiom,
% 49.33/49.50    (![A:$i]:
% 49.33/49.50     ( ( l1_pre_topc @ A ) =>
% 49.33/49.50       ( ![B:$i]:
% 49.33/49.50         ( ( m1_pre_topc @ B @ A ) =>
% 49.33/49.50           ( m1_subset_1 @
% 49.33/49.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 49.33/49.50  thf('311', plain,
% 49.33/49.50      (![X42 : $i, X43 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X42 @ X43)
% 49.33/49.50          | (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 49.33/49.50             (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 49.33/49.50          | ~ (l1_pre_topc @ X43))),
% 49.33/49.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 49.33/49.50  thf('312', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 49.33/49.50             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['310', '311'])).
% 49.33/49.50  thf('313', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 49.33/49.50             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0))))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['309', '312'])).
% 49.33/49.50  thf('314', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (v2_pre_topc @ X0)
% 49.33/49.50          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 49.33/49.50             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0))))
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['313'])).
% 49.33/49.50  thf(t3_subset, axiom,
% 49.33/49.50    (![A:$i,B:$i]:
% 49.33/49.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 49.33/49.50  thf('315', plain,
% 49.33/49.50      (![X3 : $i, X4 : $i]:
% 49.33/49.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 49.33/49.50      inference('cnf', [status(esa)], [t3_subset])).
% 49.33/49.50  thf('316', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 49.33/49.50             (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['314', '315'])).
% 49.33/49.50  thf('317', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['238'])).
% 49.33/49.50  thf('318', plain,
% 49.33/49.50      (![X42 : $i, X43 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X42 @ X43)
% 49.33/49.50          | (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 49.33/49.50             (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 49.33/49.50          | ~ (l1_pre_topc @ X43))),
% 49.33/49.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 49.33/49.50  thf('319', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (m1_subset_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)) @ 
% 49.33/49.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['317', '318'])).
% 49.33/49.50  thf('320', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_subset_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)) @ 
% 49.33/49.50           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['319'])).
% 49.33/49.50  thf('321', plain,
% 49.33/49.50      (![X3 : $i, X4 : $i]:
% 49.33/49.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 49.33/49.50      inference('cnf', [status(esa)], [t3_subset])).
% 49.33/49.50  thf('322', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)) @ 
% 49.33/49.50             (u1_struct_0 @ X0)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['320', '321'])).
% 49.33/49.50  thf(d10_xboole_0, axiom,
% 49.33/49.50    (![A:$i,B:$i]:
% 49.33/49.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 49.33/49.50  thf('323', plain,
% 49.33/49.50      (![X0 : $i, X2 : $i]:
% 49.33/49.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 49.33/49.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 49.33/49.50  thf('324', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))
% 49.33/49.50          | ((u1_struct_0 @ X0) = (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['322', '323'])).
% 49.33/49.50  thf('325', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | ((u1_struct_0 @ X0) = (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['316', '324'])).
% 49.33/49.50  thf('326', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (((u1_struct_0 @ X0) = (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['325'])).
% 49.33/49.50  thf('327', plain,
% 49.33/49.50      ((((u1_struct_0 @ sk_D)
% 49.33/49.50          = (u1_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))
% 49.33/49.50        | ~ (v2_pre_topc @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_D))),
% 49.33/49.50      inference('sup+', [status(thm)], ['305', '326'])).
% 49.33/49.50  thf('328', plain, ((v2_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['278', '279', '280'])).
% 49.33/49.50  thf('329', plain, ((l1_pre_topc @ sk_D)),
% 49.33/49.50      inference('demod', [status(thm)], ['249', '250'])).
% 49.33/49.50  thf('330', plain,
% 49.33/49.50      ((((u1_struct_0 @ sk_D)
% 49.33/49.50          = (u1_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['327', '328', '329'])).
% 49.33/49.50  thf('331', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('332', plain,
% 49.33/49.50      (((u1_struct_0 @ sk_D)
% 49.33/49.50         = (u1_struct_0 @ 
% 49.33/49.50            (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 49.33/49.50      inference('clc', [status(thm)], ['330', '331'])).
% 49.33/49.50  thf('333', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 49.33/49.50         (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('demod', [status(thm)], ['231', '332'])).
% 49.33/49.50  thf('334', plain,
% 49.33/49.50      ((((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.33/49.50         | (v2_struct_0 @ 
% 49.33/49.50            (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['221', '333'])).
% 49.33/49.50  thf('335', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['205', '206'])).
% 49.33/49.50  thf('336', plain,
% 49.33/49.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X30 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X30)
% 49.33/49.50          | ~ (l1_pre_topc @ X31)
% 49.33/49.50          | (v2_struct_0 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X32)
% 49.33/49.50          | ~ (m1_pre_topc @ X32 @ X31)
% 49.33/49.50          | ~ (v2_struct_0 @ (k1_tsep_1 @ X31 @ X30 @ X32)))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.33/49.50  thf('337', plain,
% 49.33/49.50      ((~ (v2_struct_0 @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['335', '336'])).
% 49.33/49.50  thf('338', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('339', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('340', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('341', plain,
% 49.33/49.50      ((~ (v2_struct_0 @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('demod', [status(thm)], ['337', '338', '339', '340'])).
% 49.33/49.50  thf('342', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | ~ (v2_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 49.33/49.50      inference('simplify', [status(thm)], ['341'])).
% 49.33/49.50  thf('343', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('344', plain,
% 49.33/49.50      ((~ (v2_struct_0 @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 49.33/49.50        | (v2_struct_0 @ sk_D))),
% 49.33/49.50      inference('clc', [status(thm)], ['342', '343'])).
% 49.33/49.50  thf('345', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('346', plain,
% 49.33/49.50      (~ (v2_struct_0 @ 
% 49.33/49.50          (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['344', '345'])).
% 49.33/49.50  thf('347', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['334', '346'])).
% 49.33/49.50  thf('348', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('349', plain,
% 49.33/49.50      ((((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 49.33/49.50         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('clc', [status(thm)], ['347', '348'])).
% 49.33/49.50  thf('350', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('351', plain,
% 49.33/49.50      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('clc', [status(thm)], ['349', '350'])).
% 49.33/49.50  thf('352', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('353', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('354', plain,
% 49.33/49.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X30 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X30)
% 49.33/49.50          | ~ (l1_pre_topc @ X31)
% 49.33/49.50          | (v2_struct_0 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X32)
% 49.33/49.50          | ~ (m1_pre_topc @ X32 @ X31)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X31 @ X30 @ X32) @ X31))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.33/49.50  thf('355', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ X0) @ sk_A)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['353', '354'])).
% 49.33/49.50  thf('356', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('357', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ X0) @ sk_A)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['355', '356'])).
% 49.33/49.50  thf('358', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E) @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['352', '357'])).
% 49.33/49.50  thf('359', plain,
% 49.33/49.50      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E) @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('simplify', [status(thm)], ['358'])).
% 49.33/49.50  thf('360', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('361', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E) @ sk_A))),
% 49.33/49.50      inference('clc', [status(thm)], ['359', '360'])).
% 49.33/49.50  thf('362', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('363', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E) @ sk_A)),
% 49.33/49.50      inference('clc', [status(thm)], ['361', '362'])).
% 49.33/49.50  thf('364', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('365', plain,
% 49.33/49.50      (![X47 : $i, X48 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X47)
% 49.33/49.50          | ~ (m1_pre_topc @ X47 @ X48)
% 49.33/49.50          | ((k1_tsep_1 @ X48 @ X47 @ X47)
% 49.33/49.50              = (g1_pre_topc @ (u1_struct_0 @ X47) @ (u1_pre_topc @ X47)))
% 49.33/49.50          | ~ (l1_pre_topc @ X48)
% 49.33/49.50          | ~ (v2_pre_topc @ X48)
% 49.33/49.50          | (v2_struct_0 @ X48))),
% 49.33/49.50      inference('cnf', [status(esa)], [t25_tmap_1])).
% 49.33/49.50  thf('366', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_A)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50        | ((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['364', '365'])).
% 49.33/49.50  thf('367', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('368', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('369', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | ((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['366', '367', '368'])).
% 49.33/49.50  thf('370', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('371', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E)
% 49.33/49.50        | ((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E))))),
% 49.33/49.50      inference('clc', [status(thm)], ['369', '370'])).
% 49.33/49.50  thf('372', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('373', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['371', '372'])).
% 49.33/49.50  thf('374', plain,
% 49.33/49.50      ((m1_pre_topc @ 
% 49.33/49.50        (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)) @ sk_A)),
% 49.33/49.50      inference('demod', [status(thm)], ['363', '373'])).
% 49.33/49.50  thf('375', plain,
% 49.33/49.50      ((![X0 : $i]:
% 49.33/49.50          ((v2_struct_0 @ sk_B)
% 49.33/49.50           | (v2_struct_0 @ sk_A)
% 49.33/49.50           | (v2_struct_0 @ X0)
% 49.33/49.50           | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50           | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['209', '219'])).
% 49.33/49.50  thf('376', plain,
% 49.33/49.50      ((((v1_funct_1 @ 
% 49.33/49.50          (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E))))
% 49.33/49.50         | (v2_struct_0 @ 
% 49.33/49.50            (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['374', '375'])).
% 49.33/49.50  thf('377', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E) @ sk_A)),
% 49.33/49.50      inference('clc', [status(thm)], ['361', '362'])).
% 49.33/49.50  thf('378', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ sk_A)
% 49.33/49.50          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 49.33/49.50              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 49.33/49.50  thf('379', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_B)
% 49.33/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E))
% 49.33/49.50            = (k7_relat_1 @ sk_C @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E))))
% 49.33/49.50        | (v2_struct_0 @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['377', '378'])).
% 49.33/49.50  thf('380', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('381', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E))
% 49.33/49.50            = (k7_relat_1 @ sk_C @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E)))))),
% 49.33/49.50      inference('clc', [status(thm)], ['379', '380'])).
% 49.33/49.50  thf('382', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('383', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E))
% 49.33/49.50         = (k7_relat_1 @ sk_C @ 
% 49.33/49.50            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_E @ sk_E))))),
% 49.33/49.50      inference('clc', [status(thm)], ['381', '382'])).
% 49.33/49.50  thf('384', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['371', '372'])).
% 49.33/49.50  thf('385', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['371', '372'])).
% 49.33/49.50  thf('386', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 49.33/49.50         (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50         = (k7_relat_1 @ sk_C @ 
% 49.33/49.50            (u1_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))))),
% 49.33/49.50      inference('demod', [status(thm)], ['383', '384', '385'])).
% 49.33/49.50  thf('387', plain,
% 49.33/49.50      (![X49 : $i]: ((m1_pre_topc @ X49 @ X49) | ~ (l1_pre_topc @ X49))),
% 49.33/49.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.33/49.50  thf('388', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X0)
% 49.33/49.50          | (m1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0) @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['238'])).
% 49.33/49.50  thf('389', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('390', plain,
% 49.33/49.50      (![X50 : $i, X51 : $i, X52 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X50 @ X51)
% 49.33/49.50          | (m1_pre_topc @ X52 @ X51)
% 49.33/49.50          | ~ (m1_pre_topc @ X52 @ X50)
% 49.33/49.50          | ~ (l1_pre_topc @ X51)
% 49.33/49.50          | ~ (v2_pre_topc @ X51))),
% 49.33/49.50      inference('cnf', [status(esa)], [t7_tsep_1])).
% 49.33/49.50  thf('391', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (v2_pre_topc @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_E)
% 49.33/49.50          | (m1_pre_topc @ X0 @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['389', '390'])).
% 49.33/49.50  thf('392', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('393', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('394', plain,
% 49.33/49.50      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_E) | (m1_pre_topc @ X0 @ sk_A))),
% 49.33/49.50      inference('demod', [status(thm)], ['391', '392', '393'])).
% 49.33/49.50  thf('395', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E) @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['388', '394'])).
% 49.33/49.50  thf('396', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('397', plain,
% 49.33/49.50      (![X21 : $i, X22 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X21 @ X22)
% 49.33/49.50          | (l1_pre_topc @ X21)
% 49.33/49.50          | ~ (l1_pre_topc @ X22))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.33/49.50  thf('398', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['396', '397'])).
% 49.33/49.50  thf('399', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('400', plain, ((l1_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['398', '399'])).
% 49.33/49.50  thf('401', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E)
% 49.33/49.50        | (m1_pre_topc @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E) @ sk_A))),
% 49.33/49.50      inference('demod', [status(thm)], ['395', '400'])).
% 49.33/49.50  thf('402', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('403', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E) @ sk_A)),
% 49.33/49.50      inference('clc', [status(thm)], ['401', '402'])).
% 49.33/49.50  thf('404', plain,
% 49.33/49.50      (![X21 : $i, X22 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X21 @ X22)
% 49.33/49.50          | (l1_pre_topc @ X21)
% 49.33/49.50          | ~ (l1_pre_topc @ X22))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.33/49.50  thf('405', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_A)
% 49.33/49.50        | (l1_pre_topc @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['403', '404'])).
% 49.33/49.50  thf('406', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('407', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['405', '406'])).
% 49.33/49.50  thf('408', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['272'])).
% 49.33/49.50  thf('409', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (l1_pre_topc @ sk_E)
% 49.33/49.50          | (v2_struct_0 @ sk_E)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_E)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['407', '408'])).
% 49.33/49.50  thf('410', plain, ((l1_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['398', '399'])).
% 49.33/49.50  thf('411', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('412', plain,
% 49.33/49.50      (![X19 : $i, X20 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X19 @ X20)
% 49.33/49.50          | (v2_pre_topc @ X19)
% 49.33/49.50          | ~ (l1_pre_topc @ X20)
% 49.33/49.50          | ~ (v2_pre_topc @ X20))),
% 49.33/49.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 49.33/49.50  thf('413', plain,
% 49.33/49.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['411', '412'])).
% 49.33/49.50  thf('414', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('415', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('416', plain, ((v2_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['413', '414', '415'])).
% 49.33/49.50  thf('417', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ sk_E)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['409', '410', '416'])).
% 49.33/49.50  thf('418', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('419', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X0 @ sk_E)
% 49.33/49.50          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['417', '418'])).
% 49.33/49.50  thf('420', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_E)
% 49.33/49.50        | (m1_pre_topc @ sk_E @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['387', '419'])).
% 49.33/49.50  thf('421', plain, ((l1_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['398', '399'])).
% 49.33/49.50  thf('422', plain, ((m1_pre_topc @ sk_E @ (k1_tsep_1 @ sk_E @ sk_E @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['420', '421'])).
% 49.33/49.50  thf('423', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         ((m1_pre_topc @ X1 @ X0)
% 49.33/49.50          | ~ (m1_pre_topc @ X1 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (l1_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['290'])).
% 49.33/49.50  thf('424', plain,
% 49.33/49.50      ((~ (l1_pre_topc @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_E)
% 49.33/49.50        | (m1_pre_topc @ sk_E @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['422', '423'])).
% 49.33/49.50  thf('425', plain, ((l1_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['398', '399'])).
% 49.33/49.50  thf('426', plain, ((v2_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['413', '414', '415'])).
% 49.33/49.50  thf('427', plain, (((v2_struct_0 @ sk_E) | (m1_pre_topc @ sk_E @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['424', '425', '426'])).
% 49.33/49.50  thf('428', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('429', plain, ((m1_pre_topc @ sk_E @ sk_E)),
% 49.33/49.50      inference('clc', [status(thm)], ['427', '428'])).
% 49.33/49.50  thf('430', plain,
% 49.33/49.50      (![X47 : $i, X48 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X47)
% 49.33/49.50          | ~ (m1_pre_topc @ X47 @ X48)
% 49.33/49.50          | ((k1_tsep_1 @ X48 @ X47 @ X47)
% 49.33/49.50              = (g1_pre_topc @ (u1_struct_0 @ X47) @ (u1_pre_topc @ X47)))
% 49.33/49.50          | ~ (l1_pre_topc @ X48)
% 49.33/49.50          | ~ (v2_pre_topc @ X48)
% 49.33/49.50          | (v2_struct_0 @ X48))),
% 49.33/49.50      inference('cnf', [status(esa)], [t25_tmap_1])).
% 49.33/49.50  thf('431', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_E)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_E)
% 49.33/49.50        | ((k1_tsep_1 @ sk_E @ sk_E @ sk_E)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('sup-', [status(thm)], ['429', '430'])).
% 49.33/49.50  thf('432', plain, ((v2_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['413', '414', '415'])).
% 49.33/49.50  thf('433', plain, ((l1_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['398', '399'])).
% 49.33/49.50  thf('434', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E)
% 49.33/49.50        | ((k1_tsep_1 @ sk_E @ sk_E @ sk_E)
% 49.33/49.50            = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['431', '432', '433'])).
% 49.33/49.50  thf('435', plain,
% 49.33/49.50      ((((k1_tsep_1 @ sk_E @ sk_E @ sk_E)
% 49.33/49.50          = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('simplify', [status(thm)], ['434'])).
% 49.33/49.50  thf('436', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('437', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_E @ sk_E @ sk_E)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['435', '436'])).
% 49.33/49.50  thf('438', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         (((u1_struct_0 @ X0) = (u1_struct_0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0))),
% 49.33/49.50      inference('simplify', [status(thm)], ['325'])).
% 49.33/49.50  thf('439', plain,
% 49.33/49.50      ((((u1_struct_0 @ sk_E)
% 49.33/49.50          = (u1_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E))))
% 49.33/49.50        | ~ (v2_pre_topc @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_E))),
% 49.33/49.50      inference('sup+', [status(thm)], ['437', '438'])).
% 49.33/49.50  thf('440', plain, ((v2_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['413', '414', '415'])).
% 49.33/49.50  thf('441', plain, ((l1_pre_topc @ sk_E)),
% 49.33/49.50      inference('demod', [status(thm)], ['398', '399'])).
% 49.33/49.50  thf('442', plain,
% 49.33/49.50      ((((u1_struct_0 @ sk_E)
% 49.33/49.50          = (u1_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E))))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['439', '440', '441'])).
% 49.33/49.50  thf('443', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('444', plain,
% 49.33/49.50      (((u1_struct_0 @ sk_E)
% 49.33/49.50         = (u1_struct_0 @ 
% 49.33/49.50            (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E))))),
% 49.33/49.50      inference('clc', [status(thm)], ['442', '443'])).
% 49.33/49.50  thf('445', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 49.33/49.50         (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('demod', [status(thm)], ['386', '444'])).
% 49.33/49.50  thf('446', plain,
% 49.33/49.50      ((((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.33/49.50         | (v2_struct_0 @ 
% 49.33/49.50            (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('demod', [status(thm)], ['376', '445'])).
% 49.33/49.50  thf('447', plain,
% 49.33/49.50      (((k1_tsep_1 @ sk_A @ sk_E @ sk_E)
% 49.33/49.50         = (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['371', '372'])).
% 49.33/49.50  thf('448', plain,
% 49.33/49.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 49.33/49.50         (~ (m1_pre_topc @ X30 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X30)
% 49.33/49.50          | ~ (l1_pre_topc @ X31)
% 49.33/49.50          | (v2_struct_0 @ X31)
% 49.33/49.50          | (v2_struct_0 @ X32)
% 49.33/49.50          | ~ (m1_pre_topc @ X32 @ X31)
% 49.33/49.50          | ~ (v2_struct_0 @ (k1_tsep_1 @ X31 @ X30 @ X32)))),
% 49.33/49.50      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.33/49.50  thf('449', plain,
% 49.33/49.50      ((~ (v2_struct_0 @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (m1_pre_topc @ sk_E @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['447', '448'])).
% 49.33/49.50  thf('450', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('451', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('452', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('453', plain,
% 49.33/49.50      ((~ (v2_struct_0 @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('demod', [status(thm)], ['449', '450', '451', '452'])).
% 49.33/49.50  thf('454', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_A)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (v2_struct_0 @ 
% 49.33/49.50             (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E))))),
% 49.33/49.50      inference('simplify', [status(thm)], ['453'])).
% 49.33/49.50  thf('455', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('456', plain,
% 49.33/49.50      ((~ (v2_struct_0 @ 
% 49.33/49.50           (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))
% 49.33/49.50        | (v2_struct_0 @ sk_E))),
% 49.33/49.50      inference('clc', [status(thm)], ['454', '455'])).
% 49.33/49.50  thf('457', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('458', plain,
% 49.33/49.50      (~ (v2_struct_0 @ 
% 49.33/49.50          (g1_pre_topc @ (u1_struct_0 @ sk_E) @ (u1_pre_topc @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['456', '457'])).
% 49.33/49.50  thf('459', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['446', '458'])).
% 49.33/49.50  thf('460', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('461', plain,
% 49.33/49.50      ((((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 49.33/49.50         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('clc', [status(thm)], ['459', '460'])).
% 49.33/49.50  thf('462', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('463', plain,
% 49.33/49.50      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('clc', [status(thm)], ['461', '462'])).
% 49.33/49.50  thf('464', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              sk_D @ sk_B)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('demod', [status(thm)], ['184', '185', '351', '463'])).
% 49.33/49.50  thf('465', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              sk_D @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['158', '464'])).
% 49.33/49.50  thf('466', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_E)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50              sk_D @ sk_B)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('simplify', [status(thm)], ['465'])).
% 49.33/49.50  thf('467', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_E)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['142', '466'])).
% 49.33/49.50  thf('468', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_E)
% 49.33/49.50         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50              sk_E @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('simplify', [status(thm)], ['467'])).
% 49.33/49.50  thf('469', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_E)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['137', '468'])).
% 49.33/49.50  thf('470', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('simplify', [status(thm)], ['469'])).
% 49.33/49.50  thf('471', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('472', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['470', '471'])).
% 49.33/49.50  thf('473', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('474', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('clc', [status(thm)], ['472', '473'])).
% 49.33/49.50  thf('475', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('476', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_E))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('clc', [status(thm)], ['474', '475'])).
% 49.33/49.50  thf('477', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('478', plain,
% 49.33/49.50      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 49.33/49.50       ~
% 49.33/49.50       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['476', '477'])).
% 49.33/49.50  thf('479', plain,
% 49.33/49.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('split', [status(esa)], ['122'])).
% 49.33/49.50  thf('480', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.33/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.33/49.50  thf('481', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('482', plain,
% 49.33/49.50      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 49.33/49.50         ((v2_struct_0 @ X37)
% 49.33/49.50          | ~ (v2_pre_topc @ X37)
% 49.33/49.50          | ~ (l1_pre_topc @ X37)
% 49.33/49.50          | (v2_struct_0 @ X38)
% 49.33/49.50          | ~ (m1_pre_topc @ X38 @ X39)
% 49.33/49.50          | ~ (v1_funct_1 @ 
% 49.33/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)))
% 49.33/49.50          | ~ (v1_funct_2 @ 
% 49.33/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.33/49.50               (u1_struct_0 @ X37))
% 49.33/49.50          | ~ (v5_pre_topc @ 
% 49.33/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.33/49.50               (k1_tsep_1 @ X39 @ X41 @ X38) @ X37)
% 49.33/49.50          | ~ (m1_subset_1 @ 
% 49.33/49.50               (k2_tmap_1 @ X39 @ X37 @ X40 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X39 @ X41 @ X38)) @ 
% 49.33/49.50                 (u1_struct_0 @ X37))))
% 49.33/49.50          | (m1_subset_1 @ (k2_tmap_1 @ X39 @ X37 @ X40 @ X38) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 49.33/49.50          | ~ (m1_subset_1 @ X40 @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 49.33/49.50          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 49.33/49.50          | ~ (v1_funct_1 @ X40)
% 49.33/49.50          | ~ (r4_tsep_1 @ X39 @ X41 @ X38)
% 49.33/49.50          | ~ (m1_pre_topc @ X41 @ X39)
% 49.33/49.50          | (v2_struct_0 @ X41)
% 49.33/49.50          | ~ (l1_pre_topc @ X39)
% 49.33/49.50          | ~ (v2_pre_topc @ X39)
% 49.33/49.50          | (v2_struct_0 @ X39))),
% 49.33/49.50      inference('cnf', [status(esa)], [t129_tmap_1])).
% 49.33/49.50  thf('483', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.33/49.50               (u1_struct_0 @ X0))))
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | ~ (v2_pre_topc @ sk_A)
% 49.33/49.50          | ~ (l1_pre_topc @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_D)
% 49.33/49.50          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 49.33/49.50          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 49.33/49.50          | ~ (v1_funct_1 @ X1)
% 49.33/49.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 49.33/49.50          | ~ (m1_subset_1 @ X1 @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 49.33/49.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 49.33/49.50          | ~ (v5_pre_topc @ 
% 49.33/49.50               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.33/49.50               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 49.33/49.50          | ~ (v1_funct_2 @ 
% 49.33/49.50               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.33/49.50               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.33/49.50               (u1_struct_0 @ X0))
% 49.33/49.50          | ~ (v1_funct_1 @ 
% 49.33/49.50               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 49.33/49.50          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_E)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0))),
% 49.33/49.50      inference('sup-', [status(thm)], ['481', '482'])).
% 49.33/49.50  thf('484', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('485', plain, ((v2_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('486', plain, ((l1_pre_topc @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('487', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('488', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('489', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('490', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('491', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('492', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('493', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('494', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('495', plain,
% 49.33/49.50      (![X0 : $i, X1 : $i]:
% 49.33/49.50         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 49.33/49.50          | (v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_D)
% 49.33/49.50          | ~ (v1_funct_1 @ X1)
% 49.33/49.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 49.33/49.50          | ~ (m1_subset_1 @ X1 @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 49.33/49.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E) @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 49.33/49.50          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 49.33/49.50          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 49.33/49.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 49.33/49.50          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 49.33/49.50          | (v2_struct_0 @ sk_E)
% 49.33/49.50          | ~ (l1_pre_topc @ X0)
% 49.33/49.50          | ~ (v2_pre_topc @ X0)
% 49.33/49.50          | (v2_struct_0 @ X0))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['483', '484', '485', '486', '487', '488', '489', '490', 
% 49.33/49.50                 '491', '492', '493', '494'])).
% 49.33/49.50  thf('496', plain,
% 49.33/49.50      ((~ (m1_subset_1 @ sk_C @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | (v2_struct_0 @ sk_B)
% 49.33/49.50        | ~ (v2_pre_topc @ sk_B)
% 49.33/49.50        | ~ (l1_pre_topc @ sk_B)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 49.33/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 49.33/49.50             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 49.33/49.50             sk_B)
% 49.33/49.50        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (m1_subset_1 @ sk_C @ 
% 49.33/49.50             (k1_zfmisc_1 @ 
% 49.33/49.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v1_funct_1 @ sk_C)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['480', '495'])).
% 49.33/49.50  thf('497', plain,
% 49.33/49.50      ((m1_subset_1 @ sk_C @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('498', plain, ((v2_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('499', plain, ((l1_pre_topc @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('500', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.33/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.33/49.50  thf('501', plain, ((v1_funct_1 @ sk_C)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('502', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.33/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.33/49.50  thf('503', plain,
% 49.33/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('504', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.33/49.50      inference('clc', [status(thm)], ['72', '73'])).
% 49.33/49.50  thf('505', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('506', plain,
% 49.33/49.50      ((m1_subset_1 @ sk_C @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('507', plain,
% 49.33/49.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('508', plain, ((v1_funct_1 @ sk_C)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('509', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_B)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.33/49.50        | (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_A))),
% 49.33/49.50      inference('demod', [status(thm)],
% 49.33/49.50                ['496', '497', '498', '499', '500', '501', '502', '503', 
% 49.33/49.50                 '504', '505', '506', '507', '508'])).
% 49.33/49.50  thf('510', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_A)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50            (k1_zfmisc_1 @ 
% 49.33/49.50             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['479', '509'])).
% 49.33/49.50  thf('511', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('512', plain,
% 49.33/49.50      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('split', [status(esa)], ['51'])).
% 49.33/49.50  thf('513', plain,
% 49.33/49.50      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('sup-', [status(thm)], ['511', '512'])).
% 49.33/49.50  thf('514', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_B)
% 49.33/49.50         | (v2_struct_0 @ sk_E)
% 49.33/49.50         | (v2_struct_0 @ sk_D)
% 49.33/49.50         | (v2_struct_0 @ sk_A)))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 49.33/49.50             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['510', '513'])).
% 49.33/49.50  thf('515', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('516', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 49.33/49.50             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('sup-', [status(thm)], ['514', '515'])).
% 49.33/49.50  thf('517', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('518', plain,
% 49.33/49.50      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 49.33/49.50             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('clc', [status(thm)], ['516', '517'])).
% 49.33/49.50  thf('519', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('520', plain,
% 49.33/49.50      (((v2_struct_0 @ sk_D))
% 49.33/49.50         <= (~
% 49.33/49.50             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 49.33/49.50             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.50      inference('clc', [status(thm)], ['518', '519'])).
% 49.33/49.50  thf('521', plain, (~ (v2_struct_0 @ sk_D)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('522', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 49.33/49.50       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('sup-', [status(thm)], ['520', '521'])).
% 49.33/49.50  thf('523', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 49.33/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('524', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 49.33/49.50       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('split', [status(esa)], ['523'])).
% 49.33/49.50  thf('525', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['478', '522', '524'])).
% 49.33/49.50  thf('526', plain,
% 49.33/49.50      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['120', '525'])).
% 49.33/49.50  thf('527', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('528', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('split', [status(esa)], ['527'])).
% 49.33/49.50  thf('529', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('530', plain,
% 49.33/49.50      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('demod', [status(thm)], ['528', '529'])).
% 49.33/49.50  thf('531', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('532', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 49.33/49.50       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('split', [status(esa)], ['531'])).
% 49.33/49.50  thf('533', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 49.33/49.50         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['478', '522', '532'])).
% 49.33/49.50  thf('534', plain,
% 49.33/49.50      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 49.33/49.50        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['530', '533'])).
% 49.33/49.50  thf('535', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('536', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 49.33/49.50         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 49.33/49.50      inference('split', [status(esa)], ['535'])).
% 49.33/49.50  thf('537', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('clc', [status(thm)], ['26', '27'])).
% 49.33/49.50  thf('538', plain,
% 49.33/49.50      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))
% 49.33/49.50         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 49.33/49.50      inference('demod', [status(thm)], ['536', '537'])).
% 49.33/49.50  thf('539', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 49.33/49.50       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('split', [status(esa)], ['122'])).
% 49.33/49.50  thf('540', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['478', '522', '539'])).
% 49.33/49.50  thf('541', plain,
% 49.33/49.50      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['538', '540'])).
% 49.33/49.50  thf('542', plain,
% 49.33/49.50      (![X0 : $i]:
% 49.33/49.50         ((v2_struct_0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ sk_D)
% 49.33/49.50          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 49.33/49.50          | (v5_pre_topc @ 
% 49.33/49.50             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 49.33/49.50             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 49.33/49.50          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 49.33/49.50          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 49.33/49.50               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 49.33/49.50          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 49.33/49.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.33/49.50          | (v2_struct_0 @ X0)
% 49.33/49.50          | (v2_struct_0 @ sk_B))),
% 49.33/49.50      inference('demod', [status(thm)], ['42', '116', '526', '534', '541'])).
% 49.33/49.50  thf('543', plain,
% 49.33/49.50      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50           (k1_zfmisc_1 @ 
% 49.33/49.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | (v2_struct_0 @ sk_B)
% 49.33/49.50        | (v2_struct_0 @ sk_E)
% 49.33/49.50        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 49.33/49.50        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 49.33/49.50        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 49.33/49.50             sk_B)
% 49.33/49.50        | (v5_pre_topc @ 
% 49.33/49.50           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 49.33/49.50           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 49.33/49.50        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 49.33/49.50        | (v2_struct_0 @ sk_D)
% 49.33/49.50        | (v2_struct_0 @ sk_A))),
% 49.33/49.50      inference('sup-', [status(thm)], ['21', '542'])).
% 49.33/49.50  thf('544', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 49.33/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('split', [status(esa)], ['166'])).
% 49.33/49.50  thf('545', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('546', plain,
% 49.33/49.50      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 49.33/49.50         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (k1_zfmisc_1 @ 
% 49.33/49.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 49.33/49.50      inference('demod', [status(thm)], ['544', '545'])).
% 49.33/49.50  thf('547', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 49.33/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('548', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 49.33/49.50       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('split', [status(esa)], ['547'])).
% 49.33/49.50  thf('549', plain,
% 49.33/49.50      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (k1_zfmisc_1 @ 
% 49.33/49.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['478', '522', '548'])).
% 49.33/49.50  thf('550', plain,
% 49.33/49.50      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50        (k1_zfmisc_1 @ 
% 49.33/49.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['546', '549'])).
% 49.33/49.50  thf('551', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('552', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('553', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('554', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 49.33/49.50         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 49.33/49.50      inference('split', [status(esa)], ['553'])).
% 49.33/49.50  thf('555', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('556', plain,
% 49.33/49.50      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))
% 49.33/49.50         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 49.33/49.50      inference('demod', [status(thm)], ['554', '555'])).
% 49.33/49.50  thf('557', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 49.33/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('558', plain,
% 49.33/49.50      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 49.33/49.50       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('split', [status(esa)], ['557'])).
% 49.33/49.50  thf('559', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['478', '522', '558'])).
% 49.33/49.50  thf('560', plain,
% 49.33/49.50      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['556', '559'])).
% 49.33/49.50  thf('561', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('562', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('563', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('split', [status(esa)], ['562'])).
% 49.33/49.50  thf('564', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('565', plain,
% 49.33/49.50      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 49.33/49.50         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 49.33/49.50      inference('demod', [status(thm)], ['563', '564'])).
% 49.33/49.50  thf('566', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 49.33/49.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('567', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 49.33/49.50       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.50      inference('split', [status(esa)], ['566'])).
% 49.33/49.50  thf('568', plain,
% 49.33/49.50      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 49.33/49.50         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 49.33/49.50      inference('sat_resolution*', [status(thm)], ['478', '522', '567'])).
% 49.33/49.50  thf('569', plain,
% 49.33/49.50      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 49.33/49.50        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 49.33/49.50      inference('simpl_trail', [status(thm)], ['565', '568'])).
% 49.33/49.50  thf('570', plain,
% 49.33/49.50      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.50         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.50      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.50  thf('571', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 49.33/49.50        | (v1_funct_1 @ sk_C))),
% 49.33/49.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.50  thf('572', plain,
% 49.33/49.50      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 49.33/49.50         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 49.33/49.50               sk_B)))),
% 49.33/49.51      inference('split', [status(esa)], ['571'])).
% 49.33/49.51  thf('573', plain,
% 49.33/49.51      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 49.33/49.51         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 49.33/49.51      inference('clc', [status(thm)], ['19', '20'])).
% 49.33/49.51  thf('574', plain,
% 49.33/49.51      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 49.33/49.51         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 49.33/49.51               sk_B)))),
% 49.33/49.51      inference('demod', [status(thm)], ['572', '573'])).
% 49.33/49.51  thf('575', plain,
% 49.33/49.51      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 49.33/49.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('576', plain,
% 49.33/49.51      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 49.33/49.51       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.51      inference('split', [status(esa)], ['575'])).
% 49.33/49.51  thf('577', plain,
% 49.33/49.51      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 49.33/49.51      inference('sat_resolution*', [status(thm)], ['478', '522', '576'])).
% 49.33/49.51  thf('578', plain,
% 49.33/49.51      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)),
% 49.33/49.51      inference('simpl_trail', [status(thm)], ['574', '577'])).
% 49.33/49.51  thf('579', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('580', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 49.33/49.51      inference('clc', [status(thm)], ['72', '73'])).
% 49.33/49.51  thf('581', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('582', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('583', plain,
% 49.33/49.51      (((v2_struct_0 @ sk_B)
% 49.33/49.51        | (v2_struct_0 @ sk_E)
% 49.33/49.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 49.33/49.51        | (v2_struct_0 @ sk_D)
% 49.33/49.51        | (v2_struct_0 @ sk_A))),
% 49.33/49.51      inference('demod', [status(thm)],
% 49.33/49.51                ['543', '550', '551', '552', '560', '561', '569', '570', 
% 49.33/49.51                 '578', '579', '580', '581', '582'])).
% 49.33/49.51  thf('584', plain,
% 49.33/49.51      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 49.33/49.51         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 49.33/49.51      inference('split', [status(esa)], ['51'])).
% 49.33/49.51  thf('585', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 49.33/49.51      inference('sat_resolution*', [status(thm)], ['478', '522'])).
% 49.33/49.51  thf('586', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 49.33/49.51      inference('simpl_trail', [status(thm)], ['584', '585'])).
% 49.33/49.51  thf('587', plain,
% 49.33/49.51      (((v2_struct_0 @ sk_A)
% 49.33/49.51        | (v2_struct_0 @ sk_D)
% 49.33/49.51        | (v2_struct_0 @ sk_E)
% 49.33/49.51        | (v2_struct_0 @ sk_B))),
% 49.33/49.51      inference('sup-', [status(thm)], ['583', '586'])).
% 49.33/49.51  thf('588', plain, (~ (v2_struct_0 @ sk_B)),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('589', plain,
% 49.33/49.51      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 49.33/49.51      inference('sup-', [status(thm)], ['587', '588'])).
% 49.33/49.51  thf('590', plain, (~ (v2_struct_0 @ sk_E)),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('591', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 49.33/49.51      inference('clc', [status(thm)], ['589', '590'])).
% 49.33/49.51  thf('592', plain, (~ (v2_struct_0 @ sk_A)),
% 49.33/49.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.33/49.51  thf('593', plain, ((v2_struct_0 @ sk_D)),
% 49.33/49.51      inference('clc', [status(thm)], ['591', '592'])).
% 49.33/49.51  thf('594', plain, ($false), inference('demod', [status(thm)], ['0', '593'])).
% 49.33/49.51  
% 49.33/49.51  % SZS output end Refutation
% 49.33/49.51  
% 49.33/49.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
