%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHIqBsKLjY

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:59 EST 2020

% Result     : Theorem 41.80s
% Output     : Refutation 41.80s
% Verified   : 
% Statistics : Number of formulae       :  302 (9082 expanded)
%              Number of leaves         :   40 (2603 expanded)
%              Depth                    :   42
%              Number of atoms          : 3367 (160818 expanded)
%              Number of equality atoms :  115 (1596 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t119_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t119_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ X22 ) )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('13',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( X12
       != ( k8_tmap_1 @ X11 @ X10 ) )
      | ( X13
       != ( u1_struct_0 @ X10 ) )
      | ( X12
        = ( k6_tmap_1 @ X11 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_tmap_1 @ X11 @ X10 )
        = ( k6_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('27',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('35',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('43',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','32','40','48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','53','54'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','53','54'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('76',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','53','54'])).

thf('80',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_tmap_1 @ X11 @ X10 )
        = ( k6_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['74','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['70','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('110',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_tmap_1 @ X11 @ X10 )
        = ( k6_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','53','54'])).

thf('122',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ X22 ) )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['120','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','65','104','134','135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf(reflexivity_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ) )).

thf('141',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_funct_2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X2 @ X3 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('144',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('145',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('152',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['142','159'])).

thf('161',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','53','54'])).

thf('162',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('163',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('165',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('166',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['160','171'])).

thf('173',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','172'])).

thf('174',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','158'])).

thf('175',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('176',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('179',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ X22 ) )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('183',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('189',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('190',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf(d12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) )
             => ( ( C
                  = ( k9_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('191',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( sk_D_1 @ X16 @ X14 @ X15 )
        = ( u1_struct_0 @ X14 ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('196',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195','196'])).

thf('198',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['187','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('202',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('203',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('204',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('205',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('206',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','158'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203','204','205','206'])).

thf('208',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('212',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) ) @ X16 @ ( k7_tmap_1 @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('213',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('215',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('216',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('217',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','158'])).

thf('220',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('221',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('222',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('223',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('224',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218','219','220','221','222','223','224'])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','228'])).

thf('230',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('231',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','232'])).

thf('234',plain,(
    ~ ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t110_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( ( u1_struct_0 @ C )
                  = B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('238',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_struct_0 @ X26 )
       != X24 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X26 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k7_tmap_1 @ X25 @ X24 ) @ X26 ) @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t110_tmap_1])).

thf('239',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( r1_tmap_1 @ X26 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ ( k7_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ X26 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['237','239'])).

thf('241',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('242',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('243',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('244',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['240','241','242','243','244','245','246'])).

thf('248',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['236','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['235','252'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('254',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('257',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('258',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['255','258'])).

thf('260',plain,(
    $false ),
    inference(demod,[status(thm)],['0','259'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHIqBsKLjY
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 41.80/42.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 41.80/42.02  % Solved by: fo/fo7.sh
% 41.80/42.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 41.80/42.02  % done 7298 iterations in 41.525s
% 41.80/42.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 41.80/42.02  % SZS output start Refutation
% 41.80/42.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 41.80/42.02  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 41.80/42.02  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 41.80/42.02  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 41.80/42.02  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 41.80/42.02  thf(sk_C_type, type, sk_C: $i).
% 41.80/42.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 41.80/42.02  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 41.80/42.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 41.80/42.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 41.80/42.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 41.80/42.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 41.80/42.02  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 41.80/42.02  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 41.80/42.02  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 41.80/42.02  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 41.80/42.02  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 41.80/42.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 41.80/42.02  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 41.80/42.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 41.80/42.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 41.80/42.02  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 41.80/42.02  thf(sk_A_type, type, sk_A: $i).
% 41.80/42.02  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 41.80/42.02  thf(sk_B_type, type, sk_B: $i).
% 41.80/42.02  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 41.80/42.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 41.80/42.02  thf(t119_tmap_1, conjecture,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 41.80/42.02           ( ![C:$i]:
% 41.80/42.02             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 41.80/42.02               ( r1_tmap_1 @
% 41.80/42.02                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 41.80/42.02                 ( k2_tmap_1 @
% 41.80/42.02                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 41.80/42.02                 C ) ) ) ) ) ))).
% 41.80/42.02  thf(zf_stmt_0, negated_conjecture,
% 41.80/42.02    (~( ![A:$i]:
% 41.80/42.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 41.80/42.02            ( l1_pre_topc @ A ) ) =>
% 41.80/42.02          ( ![B:$i]:
% 41.80/42.02            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 41.80/42.02              ( ![C:$i]:
% 41.80/42.02                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 41.80/42.02                  ( r1_tmap_1 @
% 41.80/42.02                    B @ ( k8_tmap_1 @ A @ B ) @ 
% 41.80/42.02                    ( k2_tmap_1 @
% 41.80/42.02                      A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 41.80/42.02                    C ) ) ) ) ) ) )),
% 41.80/42.02    inference('cnf.neg', [status(esa)], [t119_tmap_1])).
% 41.80/42.02  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf(t1_tsep_1, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( l1_pre_topc @ A ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( m1_pre_topc @ B @ A ) =>
% 41.80/42.02           ( m1_subset_1 @
% 41.80/42.02             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 41.80/42.02  thf('2', plain,
% 41.80/42.02      (![X28 : $i, X29 : $i]:
% 41.80/42.02         (~ (m1_pre_topc @ X28 @ X29)
% 41.80/42.02          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 41.80/42.02             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 41.80/42.02          | ~ (l1_pre_topc @ X29))),
% 41.80/42.02      inference('cnf', [status(esa)], [t1_tsep_1])).
% 41.80/42.02  thf('3', plain,
% 41.80/42.02      ((~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 41.80/42.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['1', '2'])).
% 41.80/42.02  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('5', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['3', '4'])).
% 41.80/42.02  thf(t104_tmap_1, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.80/42.02           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 41.80/42.02             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 41.80/42.02  thf('6', plain,
% 41.80/42.02      (![X22 : $i, X23 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.80/42.02          | ((u1_struct_0 @ (k6_tmap_1 @ X23 @ X22)) = (u1_struct_0 @ X23))
% 41.80/42.02          | ~ (l1_pre_topc @ X23)
% 41.80/42.02          | ~ (v2_pre_topc @ X23)
% 41.80/42.02          | (v2_struct_0 @ X23))),
% 41.80/42.02      inference('cnf', [status(esa)], [t104_tmap_1])).
% 41.80/42.02  thf('7', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02            = (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['5', '6'])).
% 41.80/42.02  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('10', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02            = (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['7', '8', '9'])).
% 41.80/42.02  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('12', plain,
% 41.80/42.02      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02         = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['10', '11'])).
% 41.80/42.02  thf(t2_tsep_1, axiom,
% 41.80/42.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 41.80/42.02  thf('13', plain,
% 41.80/42.02      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 41.80/42.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 41.80/42.02  thf('14', plain,
% 41.80/42.02      (![X28 : $i, X29 : $i]:
% 41.80/42.02         (~ (m1_pre_topc @ X28 @ X29)
% 41.80/42.02          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 41.80/42.02             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 41.80/42.02          | ~ (l1_pre_topc @ X29))),
% 41.80/42.02      inference('cnf', [status(esa)], [t1_tsep_1])).
% 41.80/42.02  thf('15', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['13', '14'])).
% 41.80/42.02  thf('16', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['15'])).
% 41.80/42.02  thf('17', plain,
% 41.80/42.02      (((m1_subset_1 @ 
% 41.80/42.02         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 41.80/42.02         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 41.80/42.02      inference('sup+', [status(thm)], ['12', '16'])).
% 41.80/42.02  thf('18', plain,
% 41.80/42.02      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02         = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['10', '11'])).
% 41.80/42.02  thf('19', plain,
% 41.80/42.02      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 41.80/42.02      inference('demod', [status(thm)], ['17', '18'])).
% 41.80/42.02  thf('20', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['3', '4'])).
% 41.80/42.02  thf(d11_tmap_1, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( m1_pre_topc @ B @ A ) =>
% 41.80/42.02           ( ![C:$i]:
% 41.80/42.02             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 41.80/42.02                 ( l1_pre_topc @ C ) ) =>
% 41.80/42.02               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 41.80/42.02                 ( ![D:$i]:
% 41.80/42.02                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.80/42.02                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 41.80/42.02                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 41.80/42.02  thf('21', plain,
% 41.80/42.02      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 41.80/42.02         (~ (m1_pre_topc @ X10 @ X11)
% 41.80/42.02          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ((X13) != (u1_struct_0 @ X10))
% 41.80/42.02          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 41.80/42.02          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 41.80/42.02          | ~ (l1_pre_topc @ X12)
% 41.80/42.02          | ~ (v2_pre_topc @ X12)
% 41.80/42.02          | ~ (v1_pre_topc @ X12)
% 41.80/42.02          | ~ (l1_pre_topc @ X11)
% 41.80/42.02          | ~ (v2_pre_topc @ X11)
% 41.80/42.02          | (v2_struct_0 @ X11))),
% 41.80/42.02      inference('cnf', [status(esa)], [d11_tmap_1])).
% 41.80/42.02  thf('22', plain,
% 41.80/42.02      (![X10 : $i, X11 : $i]:
% 41.80/42.02         ((v2_struct_0 @ X11)
% 41.80/42.02          | ~ (v2_pre_topc @ X11)
% 41.80/42.02          | ~ (l1_pre_topc @ X11)
% 41.80/42.02          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 41.80/42.02               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 41.80/42.02          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 41.80/42.02          | ~ (m1_pre_topc @ X10 @ X11))),
% 41.80/42.02      inference('simplify', [status(thm)], ['21'])).
% 41.80/42.02  thf('23', plain,
% 41.80/42.02      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_B)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['20', '22'])).
% 41.80/42.02  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf(dt_k8_tmap_1, axiom,
% 41.80/42.02    (![A:$i,B:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 41.80/42.02         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 41.80/42.02       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 41.80/42.02         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 41.80/42.02         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 41.80/42.02  thf('26', plain,
% 41.80/42.02      (![X20 : $i, X21 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X20)
% 41.80/42.02          | ~ (v2_pre_topc @ X20)
% 41.80/42.02          | (v2_struct_0 @ X20)
% 41.80/42.02          | ~ (m1_pre_topc @ X21 @ X20)
% 41.80/42.02          | (l1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 41.80/42.02  thf('27', plain,
% 41.80/42.02      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['25', '26'])).
% 41.80/42.02  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('30', plain,
% 41.80/42.02      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['27', '28', '29'])).
% 41.80/42.02  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('32', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 41.80/42.02      inference('clc', [status(thm)], ['30', '31'])).
% 41.80/42.02  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('34', plain,
% 41.80/42.02      (![X20 : $i, X21 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X20)
% 41.80/42.02          | ~ (v2_pre_topc @ X20)
% 41.80/42.02          | (v2_struct_0 @ X20)
% 41.80/42.02          | ~ (m1_pre_topc @ X21 @ X20)
% 41.80/42.02          | (v2_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 41.80/42.02  thf('35', plain,
% 41.80/42.02      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['33', '34'])).
% 41.80/42.02  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('38', plain,
% 41.80/42.02      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['35', '36', '37'])).
% 41.80/42.02  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('40', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 41.80/42.02      inference('clc', [status(thm)], ['38', '39'])).
% 41.80/42.02  thf('41', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('42', plain,
% 41.80/42.02      (![X20 : $i, X21 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X20)
% 41.80/42.02          | ~ (v2_pre_topc @ X20)
% 41.80/42.02          | (v2_struct_0 @ X20)
% 41.80/42.02          | ~ (m1_pre_topc @ X21 @ X20)
% 41.80/42.02          | (v1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 41.80/42.02  thf('43', plain,
% 41.80/42.02      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['41', '42'])).
% 41.80/42.02  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('46', plain,
% 41.80/42.02      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['43', '44', '45'])).
% 41.80/42.02  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('48', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 41.80/42.02      inference('clc', [status(thm)], ['46', '47'])).
% 41.80/42.02  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('51', plain,
% 41.80/42.02      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)],
% 41.80/42.02                ['23', '24', '32', '40', '48', '49', '50'])).
% 41.80/42.02  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('53', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['51', '52'])).
% 41.80/42.02  thf('54', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 41.80/42.02      inference('clc', [status(thm)], ['30', '31'])).
% 41.80/42.02  thf('55', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['19', '53', '54'])).
% 41.80/42.02  thf(dt_k7_tmap_1, axiom,
% 41.80/42.02    (![A:$i,B:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 41.80/42.02         ( l1_pre_topc @ A ) & 
% 41.80/42.02         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 41.80/42.02       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 41.80/42.02         ( v1_funct_2 @
% 41.80/42.02           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 41.80/42.02           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 41.80/42.02         ( m1_subset_1 @
% 41.80/42.02           ( k7_tmap_1 @ A @ B ) @ 
% 41.80/42.02           ( k1_zfmisc_1 @
% 41.80/42.02             ( k2_zfmisc_1 @
% 41.80/42.02               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 41.80/42.02  thf('56', plain,
% 41.80/42.02      (![X18 : $i, X19 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X18)
% 41.80/42.02          | ~ (v2_pre_topc @ X18)
% 41.80/42.02          | (v2_struct_0 @ X18)
% 41.80/42.02          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 41.80/42.02          | (m1_subset_1 @ (k7_tmap_1 @ X18 @ X19) @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ 
% 41.80/42.02               (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 41.80/42.02  thf('57', plain,
% 41.80/42.02      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02         (k1_zfmisc_1 @ 
% 41.80/42.02          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['55', '56'])).
% 41.80/42.02  thf('58', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['19', '53', '54'])).
% 41.80/42.02  thf(d10_tmap_1, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.80/42.02           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 41.80/42.02  thf('59', plain,
% 41.80/42.02      (![X8 : $i, X9 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 41.80/42.02          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 41.80/42.02          | ~ (l1_pre_topc @ X9)
% 41.80/42.02          | ~ (v2_pre_topc @ X9)
% 41.80/42.02          | (v2_struct_0 @ X9))),
% 41.80/42.02      inference('cnf', [status(esa)], [d10_tmap_1])).
% 41.80/42.02  thf('60', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['58', '59'])).
% 41.80/42.02  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('63', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('demod', [status(thm)], ['60', '61', '62'])).
% 41.80/42.02  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('65', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['63', '64'])).
% 41.80/42.02  thf('66', plain,
% 41.80/42.02      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 41.80/42.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 41.80/42.02  thf('67', plain,
% 41.80/42.02      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 41.80/42.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 41.80/42.02  thf('68', plain,
% 41.80/42.02      (![X20 : $i, X21 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X20)
% 41.80/42.02          | ~ (v2_pre_topc @ X20)
% 41.80/42.02          | (v2_struct_0 @ X20)
% 41.80/42.02          | ~ (m1_pre_topc @ X21 @ X20)
% 41.80/42.02          | (v1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 41.80/42.02  thf('69', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('sup-', [status(thm)], ['67', '68'])).
% 41.80/42.02  thf('70', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['69'])).
% 41.80/42.02  thf('71', plain,
% 41.80/42.02      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 41.80/42.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 41.80/42.02  thf('72', plain,
% 41.80/42.02      (![X20 : $i, X21 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X20)
% 41.80/42.02          | ~ (v2_pre_topc @ X20)
% 41.80/42.02          | (v2_struct_0 @ X20)
% 41.80/42.02          | ~ (m1_pre_topc @ X21 @ X20)
% 41.80/42.02          | (v2_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 41.80/42.02  thf('73', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('sup-', [status(thm)], ['71', '72'])).
% 41.80/42.02  thf('74', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['73'])).
% 41.80/42.02  thf('75', plain,
% 41.80/42.02      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 41.80/42.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 41.80/42.02  thf('76', plain,
% 41.80/42.02      (![X20 : $i, X21 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X20)
% 41.80/42.02          | ~ (v2_pre_topc @ X20)
% 41.80/42.02          | (v2_struct_0 @ X20)
% 41.80/42.02          | ~ (m1_pre_topc @ X21 @ X20)
% 41.80/42.02          | (l1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 41.80/42.02  thf('77', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('sup-', [status(thm)], ['75', '76'])).
% 41.80/42.02  thf('78', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['77'])).
% 41.80/42.02  thf('79', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['19', '53', '54'])).
% 41.80/42.02  thf('80', plain,
% 41.80/42.02      (![X10 : $i, X11 : $i]:
% 41.80/42.02         ((v2_struct_0 @ X11)
% 41.80/42.02          | ~ (v2_pre_topc @ X11)
% 41.80/42.02          | ~ (l1_pre_topc @ X11)
% 41.80/42.02          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 41.80/42.02               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 41.80/42.02          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 41.80/42.02          | ~ (m1_pre_topc @ X10 @ X11))),
% 41.80/42.02      inference('simplify', [status(thm)], ['21'])).
% 41.80/42.02  thf('81', plain,
% 41.80/42.02      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['79', '80'])).
% 41.80/42.02  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('84', plain,
% 41.80/42.02      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['81', '82', '83'])).
% 41.80/42.02  thf('85', plain,
% 41.80/42.02      ((~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['78', '84'])).
% 41.80/42.02  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('88', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['85', '86', '87'])).
% 41.80/42.02  thf('89', plain,
% 41.80/42.02      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('simplify', [status(thm)], ['88'])).
% 41.80/42.02  thf('90', plain,
% 41.80/42.02      ((~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['74', '89'])).
% 41.80/42.02  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('93', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['90', '91', '92'])).
% 41.80/42.02  thf('94', plain,
% 41.80/42.02      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('simplify', [status(thm)], ['93'])).
% 41.80/42.02  thf('95', plain,
% 41.80/42.02      ((~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['70', '94'])).
% 41.80/42.02  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('98', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['95', '96', '97'])).
% 41.80/42.02  thf('99', plain,
% 41.80/42.02      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('simplify', [status(thm)], ['98'])).
% 41.80/42.02  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('101', plain,
% 41.80/42.02      ((((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['99', '100'])).
% 41.80/42.02  thf('102', plain,
% 41.80/42.02      ((~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ((k8_tmap_1 @ sk_A @ sk_A)
% 41.80/42.02            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['66', '101'])).
% 41.80/42.02  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('104', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['102', '103'])).
% 41.80/42.02  thf('105', plain,
% 41.80/42.02      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 41.80/42.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 41.80/42.02  thf('106', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['77'])).
% 41.80/42.02  thf('107', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['73'])).
% 41.80/42.02  thf('108', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['69'])).
% 41.80/42.02  thf('109', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['15'])).
% 41.80/42.02  thf('110', plain,
% 41.80/42.02      (![X10 : $i, X11 : $i]:
% 41.80/42.02         ((v2_struct_0 @ X11)
% 41.80/42.02          | ~ (v2_pre_topc @ X11)
% 41.80/42.02          | ~ (l1_pre_topc @ X11)
% 41.80/42.02          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 41.80/42.02          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 41.80/42.02               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 41.80/42.02          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 41.80/42.02          | ~ (m1_pre_topc @ X10 @ X11))),
% 41.80/42.02      inference('simplify', [status(thm)], ['21'])).
% 41.80/42.02  thf('111', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0))),
% 41.80/42.02      inference('sup-', [status(thm)], ['109', '110'])).
% 41.80/42.02  thf('112', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         ((v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['111'])).
% 41.80/42.02  thf('113', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0))),
% 41.80/42.02      inference('sup-', [status(thm)], ['108', '112'])).
% 41.80/42.02  thf('114', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['113'])).
% 41.80/42.02  thf('115', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['107', '114'])).
% 41.80/42.02  thf('116', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['115'])).
% 41.80/42.02  thf('117', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['106', '116'])).
% 41.80/42.02  thf('118', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (m1_pre_topc @ X0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['117'])).
% 41.80/42.02  thf('119', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['105', '118'])).
% 41.80/42.02  thf('120', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['119'])).
% 41.80/42.02  thf('121', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['19', '53', '54'])).
% 41.80/42.02  thf('122', plain,
% 41.80/42.02      (![X22 : $i, X23 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.80/42.02          | ((u1_struct_0 @ (k6_tmap_1 @ X23 @ X22)) = (u1_struct_0 @ X23))
% 41.80/42.02          | ~ (l1_pre_topc @ X23)
% 41.80/42.02          | ~ (v2_pre_topc @ X23)
% 41.80/42.02          | (v2_struct_0 @ X23))),
% 41.80/42.02      inference('cnf', [status(esa)], [t104_tmap_1])).
% 41.80/42.02  thf('123', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02            = (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['121', '122'])).
% 41.80/42.02  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('126', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02            = (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['123', '124', '125'])).
% 41.80/42.02  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('128', plain,
% 41.80/42.02      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02         = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['126', '127'])).
% 41.80/42.02  thf('129', plain,
% 41.80/42.02      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup+', [status(thm)], ['120', '128'])).
% 41.80/42.02  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('132', plain,
% 41.80/42.02      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['129', '130', '131'])).
% 41.80/42.02  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('134', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['132', '133'])).
% 41.80/42.02  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('137', plain,
% 41.80/42.02      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02         (k1_zfmisc_1 @ 
% 41.80/42.02          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)],
% 41.80/42.02                ['57', '65', '104', '134', '135', '136'])).
% 41.80/42.02  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('139', plain,
% 41.80/42.02      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (k1_zfmisc_1 @ 
% 41.80/42.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('clc', [status(thm)], ['137', '138'])).
% 41.80/42.02  thf('140', plain,
% 41.80/42.02      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (k1_zfmisc_1 @ 
% 41.80/42.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('clc', [status(thm)], ['137', '138'])).
% 41.80/42.02  thf(reflexivity_r1_funct_2, axiom,
% 41.80/42.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 41.80/42.02     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 41.80/42.02         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 41.80/42.02         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 41.80/42.02         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 41.80/42.02         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 41.80/42.02       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 41.80/42.02  thf('141', plain,
% 41.80/42.02      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 41.80/42.02         ((r1_funct_2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6)
% 41.80/42.02          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3)))
% 41.80/42.02          | ~ (v1_funct_2 @ X6 @ X2 @ X3)
% 41.80/42.02          | ~ (v1_funct_1 @ X6)
% 41.80/42.02          | (v1_xboole_0 @ X5)
% 41.80/42.02          | (v1_xboole_0 @ X3)
% 41.80/42.02          | ~ (v1_funct_1 @ X7)
% 41.80/42.02          | ~ (v1_funct_2 @ X7 @ X4 @ X5)
% 41.80/42.02          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 41.80/42.02      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 41.80/42.02  thf('142', plain,
% 41.80/42.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 41.80/42.02          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 41.80/42.02          | ~ (v1_funct_1 @ X2)
% 41.80/42.02          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02          | (v1_xboole_0 @ X0)
% 41.80/42.02          | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 41.80/42.02          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 41.80/42.02             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['140', '141'])).
% 41.80/42.02  thf('143', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['3', '4'])).
% 41.80/42.02  thf('144', plain,
% 41.80/42.02      (![X18 : $i, X19 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X18)
% 41.80/42.02          | ~ (v2_pre_topc @ X18)
% 41.80/42.02          | (v2_struct_0 @ X18)
% 41.80/42.02          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 41.80/42.02          | (v1_funct_1 @ (k7_tmap_1 @ X18 @ X19)))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 41.80/42.02  thf('145', plain,
% 41.80/42.02      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['143', '144'])).
% 41.80/42.02  thf('146', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('148', plain,
% 41.80/42.02      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['145', '146', '147'])).
% 41.80/42.02  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('150', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['148', '149'])).
% 41.80/42.02  thf('151', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['3', '4'])).
% 41.80/42.02  thf('152', plain,
% 41.80/42.02      (![X8 : $i, X9 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 41.80/42.02          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 41.80/42.02          | ~ (l1_pre_topc @ X9)
% 41.80/42.02          | ~ (v2_pre_topc @ X9)
% 41.80/42.02          | (v2_struct_0 @ X9))),
% 41.80/42.02      inference('cnf', [status(esa)], [d10_tmap_1])).
% 41.80/42.02  thf('153', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 41.80/42.02            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('sup-', [status(thm)], ['151', '152'])).
% 41.80/42.02  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('156', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 41.80/42.02            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('demod', [status(thm)], ['153', '154', '155'])).
% 41.80/42.02  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('158', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['156', '157'])).
% 41.80/42.02  thf('159', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['150', '158'])).
% 41.80/42.02  thf('160', plain,
% 41.80/42.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 41.80/42.02          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 41.80/42.02          | ~ (v1_funct_1 @ X2)
% 41.80/42.02          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02          | (v1_xboole_0 @ X0)
% 41.80/42.02          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 41.80/42.02          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 41.80/42.02             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('demod', [status(thm)], ['142', '159'])).
% 41.80/42.02  thf('161', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['19', '53', '54'])).
% 41.80/42.02  thf('162', plain,
% 41.80/42.02      (![X18 : $i, X19 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X18)
% 41.80/42.02          | ~ (v2_pre_topc @ X18)
% 41.80/42.02          | (v2_struct_0 @ X18)
% 41.80/42.02          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 41.80/42.02          | (v1_funct_2 @ (k7_tmap_1 @ X18 @ X19) @ (u1_struct_0 @ X18) @ 
% 41.80/42.02             (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 41.80/42.02  thf('163', plain,
% 41.80/42.02      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02         (u1_struct_0 @ sk_A) @ 
% 41.80/42.02         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['161', '162'])).
% 41.80/42.02  thf('164', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['63', '64'])).
% 41.80/42.02  thf('165', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['102', '103'])).
% 41.80/42.02  thf('166', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['132', '133'])).
% 41.80/42.02  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('169', plain,
% 41.80/42.02      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)],
% 41.80/42.02                ['163', '164', '165', '166', '167', '168'])).
% 41.80/42.02  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('171', plain,
% 41.80/42.02      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['169', '170'])).
% 41.80/42.02  thf('172', plain,
% 41.80/42.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 41.80/42.02          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 41.80/42.02          | ~ (v1_funct_1 @ X2)
% 41.80/42.02          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02          | (v1_xboole_0 @ X0)
% 41.80/42.02          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 41.80/42.02             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('demod', [status(thm)], ['160', '171'])).
% 41.80/42.02  thf('173', plain,
% 41.80/42.02      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['139', '172'])).
% 41.80/42.02  thf('174', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['150', '158'])).
% 41.80/42.02  thf('175', plain,
% 41.80/42.02      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['169', '170'])).
% 41.80/42.02  thf('176', plain,
% 41.80/42.02      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['173', '174', '175'])).
% 41.80/42.02  thf('177', plain,
% 41.80/42.02      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('simplify', [status(thm)], ['176'])).
% 41.80/42.02  thf('178', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['15'])).
% 41.80/42.02  thf('179', plain,
% 41.80/42.02      (![X22 : $i, X23 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.80/42.02          | ((u1_struct_0 @ (k6_tmap_1 @ X23 @ X22)) = (u1_struct_0 @ X23))
% 41.80/42.02          | ~ (l1_pre_topc @ X23)
% 41.80/42.02          | ~ (v2_pre_topc @ X23)
% 41.80/42.02          | (v2_struct_0 @ X23))),
% 41.80/42.02      inference('cnf', [status(esa)], [t104_tmap_1])).
% 41.80/42.02  thf('180', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02              = (u1_struct_0 @ X0)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['178', '179'])).
% 41.80/42.02  thf('181', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 41.80/42.02            = (u1_struct_0 @ X0))
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['180'])).
% 41.80/42.02  thf('182', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['15'])).
% 41.80/42.02  thf('183', plain,
% 41.80/42.02      (![X18 : $i, X19 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X18)
% 41.80/42.02          | ~ (v2_pre_topc @ X18)
% 41.80/42.02          | (v2_struct_0 @ X18)
% 41.80/42.02          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 41.80/42.02          | (m1_subset_1 @ (k7_tmap_1 @ X18 @ X19) @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ 
% 41.80/42.02               (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 41.80/42.02  thf('184', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (l1_pre_topc @ X0)
% 41.80/42.02          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('sup-', [status(thm)], ['182', '183'])).
% 41.80/42.02  thf('185', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 41.80/42.02               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))
% 41.80/42.02          | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('simplify', [status(thm)], ['184'])).
% 41.80/42.02  thf('186', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         ((m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 41.80/42.02           (k1_zfmisc_1 @ 
% 41.80/42.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (v2_pre_topc @ X0))),
% 41.80/42.02      inference('sup+', [status(thm)], ['181', '185'])).
% 41.80/42.02  thf('187', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (v2_pre_topc @ X0)
% 41.80/42.02          | (v2_struct_0 @ X0)
% 41.80/42.02          | ~ (l1_pre_topc @ X0)
% 41.80/42.02          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 41.80/42.02      inference('simplify', [status(thm)], ['186'])).
% 41.80/42.02  thf('188', plain,
% 41.80/42.02      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02         = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['10', '11'])).
% 41.80/42.02  thf('189', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['51', '52'])).
% 41.80/42.02  thf('190', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['188', '189'])).
% 41.80/42.02  thf(d12_tmap_1, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( m1_pre_topc @ B @ A ) =>
% 41.80/42.02           ( ![C:$i]:
% 41.80/42.02             ( ( ( v1_funct_1 @ C ) & 
% 41.80/42.02                 ( v1_funct_2 @
% 41.80/42.02                   C @ ( u1_struct_0 @ A ) @ 
% 41.80/42.02                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 41.80/42.02                 ( m1_subset_1 @
% 41.80/42.02                   C @ 
% 41.80/42.02                   ( k1_zfmisc_1 @
% 41.80/42.02                     ( k2_zfmisc_1 @
% 41.80/42.02                       ( u1_struct_0 @ A ) @ 
% 41.80/42.02                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 41.80/42.02               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 41.80/42.02                 ( ![D:$i]:
% 41.80/42.02                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.80/42.02                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 41.80/42.02                       ( r1_funct_2 @
% 41.80/42.02                         ( u1_struct_0 @ A ) @ 
% 41.80/42.02                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 41.80/42.02                         ( u1_struct_0 @ A ) @ 
% 41.80/42.02                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 41.80/42.02                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 41.80/42.02  thf('191', plain,
% 41.80/42.02      (![X14 : $i, X15 : $i, X16 : $i]:
% 41.80/42.02         (~ (m1_pre_topc @ X14 @ X15)
% 41.80/42.02          | ((sk_D_1 @ X16 @ X14 @ X15) = (u1_struct_0 @ X14))
% 41.80/42.02          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 41.80/42.02          | ~ (m1_subset_1 @ X16 @ 
% 41.80/42.02               (k1_zfmisc_1 @ 
% 41.80/42.02                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 41.80/42.02                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 41.80/42.02          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 41.80/42.02               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 41.80/42.02          | ~ (v1_funct_1 @ X16)
% 41.80/42.02          | ~ (l1_pre_topc @ X15)
% 41.80/42.02          | ~ (v2_pre_topc @ X15)
% 41.80/42.02          | (v2_struct_0 @ X15))),
% 41.80/42.02      inference('cnf', [status(esa)], [d12_tmap_1])).
% 41.80/42.02  thf('192', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X0 @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 41.80/42.02          | (v2_struct_0 @ sk_A)
% 41.80/42.02          | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02          | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02          | ~ (v1_funct_1 @ X0)
% 41.80/42.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 41.80/42.02          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))
% 41.80/42.02          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['190', '191'])).
% 41.80/42.02  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('195', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['188', '189'])).
% 41.80/42.02  thf('196', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('197', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X0 @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 41.80/42.02          | (v2_struct_0 @ sk_A)
% 41.80/42.02          | ~ (v1_funct_1 @ X0)
% 41.80/42.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 41.80/42.02          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('demod', [status(thm)], ['192', '193', '194', '195', '196'])).
% 41.80/42.02  thf('198', plain,
% 41.80/42.02      ((~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ((sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 41.80/42.02            = (u1_struct_0 @ sk_B))
% 41.80/42.02        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02            = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['187', '197'])).
% 41.80/42.02  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('200', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('201', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['63', '64'])).
% 41.80/42.02  thf('202', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['63', '64'])).
% 41.80/42.02  thf('203', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['63', '64'])).
% 41.80/42.02  thf('204', plain,
% 41.80/42.02      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['169', '170'])).
% 41.80/42.02  thf('205', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['63', '64'])).
% 41.80/42.02  thf('206', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['150', '158'])).
% 41.80/42.02  thf('207', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 41.80/42.02            = (u1_struct_0 @ sk_B))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)],
% 41.80/42.02                ['198', '199', '200', '201', '202', '203', '204', '205', '206'])).
% 41.80/42.02  thf('208', plain,
% 41.80/42.02      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 41.80/42.02            = (u1_struct_0 @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('simplify', [status(thm)], ['207'])).
% 41.80/42.02  thf('209', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('210', plain,
% 41.80/42.02      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 41.80/42.02          = (u1_struct_0 @ sk_B))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['208', '209'])).
% 41.80/42.02  thf('211', plain,
% 41.80/42.02      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 41.80/42.02          = (u1_struct_0 @ sk_B))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['208', '209'])).
% 41.80/42.02  thf('212', plain,
% 41.80/42.02      (![X14 : $i, X15 : $i, X16 : $i]:
% 41.80/42.02         (~ (m1_pre_topc @ X14 @ X15)
% 41.80/42.02          | ~ (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 41.80/42.02               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 41.80/42.02               (u1_struct_0 @ (k6_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15))) @ 
% 41.80/42.02               X16 @ (k7_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15)))
% 41.80/42.02          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 41.80/42.02          | ~ (m1_subset_1 @ X16 @ 
% 41.80/42.02               (k1_zfmisc_1 @ 
% 41.80/42.02                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 41.80/42.02                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 41.80/42.02          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 41.80/42.02               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 41.80/42.02          | ~ (v1_funct_1 @ X16)
% 41.80/42.02          | ~ (l1_pre_topc @ X15)
% 41.80/42.02          | ~ (v2_pre_topc @ X15)
% 41.80/42.02          | (v2_struct_0 @ X15))),
% 41.80/42.02      inference('cnf', [status(esa)], [d12_tmap_1])).
% 41.80/42.02  thf('213', plain,
% 41.80/42.02      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02           (k7_tmap_1 @ sk_A @ 
% 41.80/42.02            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02        | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 41.80/42.02        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (k1_zfmisc_1 @ 
% 41.80/42.02              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['211', '212'])).
% 41.80/42.02  thf('214', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['188', '189'])).
% 41.80/42.02  thf('215', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['51', '52'])).
% 41.80/42.02  thf('216', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['188', '189'])).
% 41.80/42.02  thf('217', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('219', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['150', '158'])).
% 41.80/42.02  thf('220', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['188', '189'])).
% 41.80/42.02  thf('221', plain,
% 41.80/42.02      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('clc', [status(thm)], ['169', '170'])).
% 41.80/42.02  thf('222', plain,
% 41.80/42.02      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['188', '189'])).
% 41.80/42.02  thf('223', plain,
% 41.80/42.02      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02        (k1_zfmisc_1 @ 
% 41.80/42.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('clc', [status(thm)], ['137', '138'])).
% 41.80/42.02  thf('224', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('225', plain,
% 41.80/42.02      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02           (k7_tmap_1 @ sk_A @ 
% 41.80/42.02            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | (v2_struct_0 @ sk_A)
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('demod', [status(thm)],
% 41.80/42.02                ['213', '214', '215', '216', '217', '218', '219', '220', 
% 41.80/42.02                 '221', '222', '223', '224'])).
% 41.80/42.02  thf('226', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (k7_tmap_1 @ sk_A @ 
% 41.80/42.02              (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))))),
% 41.80/42.02      inference('simplify', [status(thm)], ['225'])).
% 41.80/42.02  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('228', plain,
% 41.80/42.02      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02           (k7_tmap_1 @ sk_A @ 
% 41.80/42.02            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['226', '227'])).
% 41.80/42.02  thf('229', plain,
% 41.80/42.02      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['210', '228'])).
% 41.80/42.02  thf('230', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['156', '157'])).
% 41.80/42.02  thf('231', plain,
% 41.80/42.02      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02           (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('demod', [status(thm)], ['229', '230'])).
% 41.80/42.02  thf('232', plain,
% 41.80/42.02      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 41.80/42.02        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 41.80/42.02             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 41.80/42.02             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 41.80/42.02      inference('simplify', [status(thm)], ['231'])).
% 41.80/42.02  thf('233', plain,
% 41.80/42.02      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 41.80/42.02        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['177', '232'])).
% 41.80/42.02  thf('234', plain,
% 41.80/42.02      (~ (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 41.80/42.02          sk_C)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('235', plain,
% 41.80/42.02      ((~ (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 41.80/42.02           sk_C)
% 41.80/42.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('sup-', [status(thm)], ['233', '234'])).
% 41.80/42.02  thf('236', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('237', plain,
% 41.80/42.02      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 41.80/42.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('demod', [status(thm)], ['3', '4'])).
% 41.80/42.02  thf(t110_tmap_1, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.80/42.02       ( ![B:$i]:
% 41.80/42.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.80/42.02           ( ![C:$i]:
% 41.80/42.02             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 41.80/42.02               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 41.80/42.02                 ( ![D:$i]:
% 41.80/42.02                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 41.80/42.02                     ( r1_tmap_1 @
% 41.80/42.02                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 41.80/42.02                       ( k2_tmap_1 @
% 41.80/42.02                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 41.80/42.02                       D ) ) ) ) ) ) ) ) ))).
% 41.80/42.02  thf('238', plain,
% 41.80/42.02      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 41.80/42.02          | ((u1_struct_0 @ X26) != (X24))
% 41.80/42.02          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 41.80/42.02          | (r1_tmap_1 @ X26 @ (k6_tmap_1 @ X25 @ X24) @ 
% 41.80/42.02             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ X24) @ 
% 41.80/42.02              (k7_tmap_1 @ X25 @ X24) @ X26) @ 
% 41.80/42.02             X27)
% 41.80/42.02          | ~ (m1_pre_topc @ X26 @ X25)
% 41.80/42.02          | (v2_struct_0 @ X26)
% 41.80/42.02          | ~ (l1_pre_topc @ X25)
% 41.80/42.02          | ~ (v2_pre_topc @ X25)
% 41.80/42.02          | (v2_struct_0 @ X25))),
% 41.80/42.02      inference('cnf', [status(esa)], [t110_tmap_1])).
% 41.80/42.02  thf('239', plain,
% 41.80/42.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 41.80/42.02         ((v2_struct_0 @ X25)
% 41.80/42.02          | ~ (v2_pre_topc @ X25)
% 41.80/42.02          | ~ (l1_pre_topc @ X25)
% 41.80/42.02          | (v2_struct_0 @ X26)
% 41.80/42.02          | ~ (m1_pre_topc @ X26 @ X25)
% 41.80/42.02          | (r1_tmap_1 @ X26 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ 
% 41.80/42.02             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ 
% 41.80/42.02              (k7_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ X26) @ 
% 41.80/42.02             X27)
% 41.80/42.02          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 41.80/42.02          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 41.80/42.02               (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 41.80/42.02      inference('simplify', [status(thm)], ['238'])).
% 41.80/42.02  thf('240', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 41.80/42.02          | (r1_tmap_1 @ sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 41.80/42.02             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 41.80/42.02              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 41.80/42.02             X0)
% 41.80/42.02          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 41.80/42.02          | (v2_struct_0 @ sk_B)
% 41.80/42.02          | ~ (l1_pre_topc @ sk_A)
% 41.80/42.02          | ~ (v2_pre_topc @ sk_A)
% 41.80/42.02          | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['237', '239'])).
% 41.80/42.02  thf('241', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['51', '52'])).
% 41.80/42.02  thf('242', plain,
% 41.80/42.02      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 41.80/42.02      inference('clc', [status(thm)], ['51', '52'])).
% 41.80/42.02  thf('243', plain,
% 41.80/42.02      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 41.80/42.02         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 41.80/42.02      inference('clc', [status(thm)], ['156', '157'])).
% 41.80/42.02  thf('244', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('245', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('246', plain, ((v2_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('247', plain,
% 41.80/42.02      (![X0 : $i]:
% 41.80/42.02         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 41.80/42.02          | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02              (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 41.80/42.02             X0)
% 41.80/42.02          | (v2_struct_0 @ sk_B)
% 41.80/42.02          | (v2_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)],
% 41.80/42.02                ['240', '241', '242', '243', '244', '245', '246'])).
% 41.80/42.02  thf('248', plain,
% 41.80/42.02      (((v2_struct_0 @ sk_A)
% 41.80/42.02        | (v2_struct_0 @ sk_B)
% 41.80/42.02        | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 41.80/42.02           sk_C))),
% 41.80/42.02      inference('sup-', [status(thm)], ['236', '247'])).
% 41.80/42.02  thf('249', plain, (~ (v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('250', plain,
% 41.80/42.02      (((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 41.80/42.02         sk_C)
% 41.80/42.02        | (v2_struct_0 @ sk_B))),
% 41.80/42.02      inference('clc', [status(thm)], ['248', '249'])).
% 41.80/42.02  thf('251', plain, (~ (v2_struct_0 @ sk_B)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf('252', plain,
% 41.80/42.02      ((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 41.80/42.02         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 41.80/42.02        sk_C)),
% 41.80/42.02      inference('clc', [status(thm)], ['250', '251'])).
% 41.80/42.02  thf('253', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 41.80/42.02      inference('demod', [status(thm)], ['235', '252'])).
% 41.80/42.02  thf(fc2_struct_0, axiom,
% 41.80/42.02    (![A:$i]:
% 41.80/42.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 41.80/42.02       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 41.80/42.02  thf('254', plain,
% 41.80/42.02      (![X1 : $i]:
% 41.80/42.02         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 41.80/42.02          | ~ (l1_struct_0 @ X1)
% 41.80/42.02          | (v2_struct_0 @ X1))),
% 41.80/42.02      inference('cnf', [status(esa)], [fc2_struct_0])).
% 41.80/42.02  thf('255', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 41.80/42.02      inference('sup-', [status(thm)], ['253', '254'])).
% 41.80/42.02  thf('256', plain, ((l1_pre_topc @ sk_A)),
% 41.80/42.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.80/42.02  thf(dt_l1_pre_topc, axiom,
% 41.80/42.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 41.80/42.02  thf('257', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 41.80/42.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 41.80/42.02  thf('258', plain, ((l1_struct_0 @ sk_A)),
% 41.80/42.02      inference('sup-', [status(thm)], ['256', '257'])).
% 41.80/42.02  thf('259', plain, ((v2_struct_0 @ sk_A)),
% 41.80/42.02      inference('demod', [status(thm)], ['255', '258'])).
% 41.80/42.02  thf('260', plain, ($false), inference('demod', [status(thm)], ['0', '259'])).
% 41.80/42.02  
% 41.80/42.02  % SZS output end Refutation
% 41.80/42.02  
% 41.80/42.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
