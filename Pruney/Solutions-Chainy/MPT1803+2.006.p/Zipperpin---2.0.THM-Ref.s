%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mikv76ocUV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:59 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  200 (2327 expanded)
%              Number of leaves         :   39 ( 689 expanded)
%              Depth                    :   25
%              Number of atoms          : 2121 (42854 expanded)
%              Number of equality atoms :   69 ( 404 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

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

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
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

thf('18',plain,(
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
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('23',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('31',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','28','36','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','15','49','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

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

thf('66',plain,(
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

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('70',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('77',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('80',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('82',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('83',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','77','88'])).

thf('90',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','89'])).

thf('91',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('92',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('93',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('96',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

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

thf('97',plain,(
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

thf('98',plain,(
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
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('102',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('106',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('107',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('111',plain,(
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

thf('112',plain,
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
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('114',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('115',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('119',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('120',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('121',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('122',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('123',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119','120','121','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','127'])).

thf('129',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('130',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','131'])).

thf('133',plain,(
    ~ ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
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

thf('137',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X24 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t110_tmap_1])).

thf('138',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( r1_tmap_1 @ X24 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','138'])).

thf('140',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('141',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('142',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('143',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['135','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','151'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('153',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('156',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('157',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['154','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['0','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mikv76ocUV
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 168 iterations in 0.500s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.98  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.75/0.98  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.75/0.98  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.98  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.98  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.75/0.98  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.75/0.98  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.75/0.98  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.75/0.98  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.75/0.98  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.75/0.98  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.98  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.98  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.75/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.98  thf(t119_tmap_1, conjecture,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.75/0.98               ( r1_tmap_1 @
% 0.75/0.98                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.75/0.98                 ( k2_tmap_1 @
% 0.75/0.98                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.75/0.98                 C ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i]:
% 0.75/0.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.98            ( l1_pre_topc @ A ) ) =>
% 0.75/0.98          ( ![B:$i]:
% 0.75/0.98            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.75/0.98              ( ![C:$i]:
% 0.75/0.98                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.75/0.98                  ( r1_tmap_1 @
% 0.75/0.98                    B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.75/0.98                    ( k2_tmap_1 @
% 0.75/0.98                      A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.75/0.98                    C ) ) ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t119_tmap_1])).
% 0.75/0.98  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(t1_tsep_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( l1_pre_topc @ A ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_pre_topc @ B @ A ) =>
% 0.75/0.98           ( m1_subset_1 @
% 0.75/0.98             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X29 : $i, X30 : $i]:
% 0.75/0.98         (~ (m1_pre_topc @ X29 @ X30)
% 0.75/0.98          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.75/0.98             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.75/0.98          | ~ (l1_pre_topc @ X30))),
% 0.75/0.98      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf(dt_k7_tmap_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.98         ( l1_pre_topc @ A ) & 
% 0.75/0.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.98       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.75/0.98         ( v1_funct_2 @
% 0.75/0.98           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.98           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.75/0.98         ( m1_subset_1 @
% 0.75/0.98           ( k7_tmap_1 @ A @ B ) @ 
% 0.75/0.98           ( k1_zfmisc_1 @
% 0.75/0.98             ( k2_zfmisc_1 @
% 0.75/0.98               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X18)
% 0.75/0.98          | ~ (v2_pre_topc @ X18)
% 0.75/0.98          | (v2_struct_0 @ X18)
% 0.75/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.75/0.98          | (m1_subset_1 @ (k7_tmap_1 @ X18 @ X19) @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ 
% 0.75/0.98               (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.75/0.98         (k1_zfmisc_1 @ 
% 0.75/0.98          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf(d10_tmap_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.75/0.98          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 0.75/0.98          | ~ (l1_pre_topc @ X9)
% 0.75/0.98          | ~ (v2_pre_topc @ X9)
% 0.75/0.98          | (v2_struct_0 @ X9))),
% 0.75/0.98      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.98  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_A)
% 0.75/0.98        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.75/0.98  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf(d11_tmap_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_pre_topc @ B @ A ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.75/0.98                 ( l1_pre_topc @ C ) ) =>
% 0.75/0.98               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.75/0.98                 ( ![D:$i]:
% 0.75/0.98                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.75/0.98                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.98         (~ (m1_pre_topc @ X10 @ X11)
% 0.75/0.98          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 0.75/0.98          | ((X13) != (u1_struct_0 @ X10))
% 0.75/0.98          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 0.75/0.98          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.75/0.98          | ~ (l1_pre_topc @ X12)
% 0.75/0.98          | ~ (v2_pre_topc @ X12)
% 0.75/0.98          | ~ (v1_pre_topc @ X12)
% 0.75/0.98          | ~ (l1_pre_topc @ X11)
% 0.75/0.98          | ~ (v2_pre_topc @ X11)
% 0.75/0.98          | (v2_struct_0 @ X11))),
% 0.75/0.98      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X10 : $i, X11 : $i]:
% 0.75/0.98         ((v2_struct_0 @ X11)
% 0.75/0.98          | ~ (v2_pre_topc @ X11)
% 0.75/0.98          | ~ (l1_pre_topc @ X11)
% 0.75/0.98          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.75/0.98          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.75/0.98          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.75/0.98          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.75/0.98               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.75/0.98          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.75/0.98          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.75/0.98      inference('simplify', [status(thm)], ['17'])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.75/0.98        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.75/0.98            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.75/0.98        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['16', '18'])).
% 0.75/0.98  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(dt_k8_tmap_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.98         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.75/0.98       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.75/0.98         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.75/0.98         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (![X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X20)
% 0.75/0.98          | ~ (v2_pre_topc @ X20)
% 0.75/0.98          | (v2_struct_0 @ X20)
% 0.75/0.98          | ~ (m1_pre_topc @ X21 @ X20)
% 0.75/0.98          | (l1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.98  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.75/0.98  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('28', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.75/0.98      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.98  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X20)
% 0.75/0.98          | ~ (v2_pre_topc @ X20)
% 0.75/0.98          | (v2_struct_0 @ X20)
% 0.75/0.98          | ~ (m1_pre_topc @ X21 @ X20)
% 0.75/0.98          | (v2_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.98  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.75/0.98  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('36', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.75/0.98      inference('clc', [status(thm)], ['34', '35'])).
% 0.75/0.98  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X20)
% 0.75/0.98          | ~ (v2_pre_topc @ X20)
% 0.75/0.98          | (v2_struct_0 @ X20)
% 0.75/0.98          | ~ (m1_pre_topc @ X21 @ X20)
% 0.75/0.98          | (v1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.98  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.75/0.98  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('44', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.75/0.98      inference('clc', [status(thm)], ['42', '43'])).
% 0.75/0.98  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)],
% 0.75/0.98                ['19', '20', '28', '36', '44', '45', '46'])).
% 0.75/0.98  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(t114_tmap_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.75/0.98           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.75/0.98             ( ![C:$i]:
% 0.75/0.98               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.75/0.98                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.75/0.98                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('51', plain,
% 0.75/0.98      (![X26 : $i, X27 : $i]:
% 0.75/0.98         ((v2_struct_0 @ X26)
% 0.75/0.98          | ~ (m1_pre_topc @ X26 @ X27)
% 0.75/0.98          | ((u1_struct_0 @ (k8_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.75/0.98          | ~ (l1_pre_topc @ X27)
% 0.75/0.98          | ~ (v2_pre_topc @ X27)
% 0.75/0.98          | (v2_struct_0 @ X27))),
% 0.75/0.98      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.75/0.98        | (v2_struct_0 @ sk_B))),
% 0.75/0.98      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.98  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_A)
% 0.75/0.98        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.75/0.98        | (v2_struct_0 @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.75/0.98  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_B)
% 0.75/0.98        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('clc', [status(thm)], ['55', '56'])).
% 0.75/0.98  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98         (k1_zfmisc_1 @ 
% 0.75/0.98          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['7', '15', '49', '59', '60', '61'])).
% 0.75/0.98  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('64', plain,
% 0.75/0.98      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('clc', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('clc', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf(reflexivity_r1_funct_2, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.98     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.75/0.98         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.75/0.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.98         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.75/0.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.98       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.75/0.98  thf('66', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.98         ((r1_funct_2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6)
% 0.75/0.98          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3)))
% 0.75/0.98          | ~ (v1_funct_2 @ X6 @ X2 @ X3)
% 0.75/0.98          | ~ (v1_funct_1 @ X6)
% 0.75/0.98          | (v1_xboole_0 @ X5)
% 0.75/0.98          | (v1_xboole_0 @ X3)
% 0.75/0.98          | ~ (v1_funct_1 @ X7)
% 0.75/0.98          | ~ (v1_funct_2 @ X7 @ X4 @ X5)
% 0.75/0.98          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.75/0.98      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.75/0.98          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.75/0.98          | ~ (v1_funct_1 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.98          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.75/0.98             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.98  thf('68', plain,
% 0.75/0.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X18)
% 0.75/0.98          | ~ (v2_pre_topc @ X18)
% 0.75/0.98          | (v2_struct_0 @ X18)
% 0.75/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.75/0.98          | (v1_funct_1 @ (k7_tmap_1 @ X18 @ X19)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['68', '69'])).
% 0.75/0.98  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('73', plain,
% 0.75/0.98      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.75/0.98  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('75', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['73', '74'])).
% 0.75/0.98  thf('76', plain,
% 0.75/0.98      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('77', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['75', '76'])).
% 0.75/0.98  thf('78', plain,
% 0.75/0.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf('79', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X18)
% 0.75/0.98          | ~ (v2_pre_topc @ X18)
% 0.75/0.98          | (v2_struct_0 @ X18)
% 0.75/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.75/0.98          | (v1_funct_2 @ (k7_tmap_1 @ X18 @ X19) @ (u1_struct_0 @ X18) @ 
% 0.75/0.98             (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.75/0.98  thf('80', plain,
% 0.75/0.98      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.75/0.98         (u1_struct_0 @ sk_A) @ 
% 0.75/0.98         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['78', '79'])).
% 0.75/0.98  thf('81', plain,
% 0.75/0.98      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('82', plain,
% 0.75/0.98      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('83', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('86', plain,
% 0.75/0.98      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['80', '81', '82', '83', '84', '85'])).
% 0.75/0.98  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('88', plain,
% 0.75/0.98      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('89', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.75/0.98          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.75/0.98          | ~ (v1_funct_1 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.75/0.98             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('demod', [status(thm)], ['67', '77', '88'])).
% 0.75/0.98  thf('90', plain,
% 0.75/0.98      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['64', '89'])).
% 0.75/0.98  thf('91', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['75', '76'])).
% 0.75/0.98  thf('92', plain,
% 0.75/0.98      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('93', plain,
% 0.75/0.98      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.75/0.98  thf('94', plain,
% 0.75/0.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['93'])).
% 0.75/0.98  thf('95', plain,
% 0.75/0.98      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('clc', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf('96', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf(d12_tmap_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_pre_topc @ B @ A ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.98                 ( v1_funct_2 @
% 0.75/0.98                   C @ ( u1_struct_0 @ A ) @ 
% 0.75/0.98                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.75/0.98                 ( m1_subset_1 @
% 0.75/0.98                   C @ 
% 0.75/0.98                   ( k1_zfmisc_1 @
% 0.75/0.98                     ( k2_zfmisc_1 @
% 0.75/0.98                       ( u1_struct_0 @ A ) @ 
% 0.75/0.98                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.75/0.98               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.75/0.98                 ( ![D:$i]:
% 0.75/0.98                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.75/0.98                       ( r1_funct_2 @
% 0.75/0.98                         ( u1_struct_0 @ A ) @ 
% 0.75/0.98                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.75/0.98                         ( u1_struct_0 @ A ) @ 
% 0.75/0.98                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.75/0.98                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('97', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.98         (~ (m1_pre_topc @ X14 @ X15)
% 0.75/0.98          | ((sk_D_1 @ X16 @ X14 @ X15) = (u1_struct_0 @ X14))
% 0.75/0.98          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 0.75/0.98          | ~ (m1_subset_1 @ X16 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.75/0.98                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.75/0.98          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 0.75/0.98               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.75/0.98          | ~ (v1_funct_1 @ X16)
% 0.75/0.98          | ~ (l1_pre_topc @ X15)
% 0.75/0.98          | ~ (v2_pre_topc @ X15)
% 0.75/0.98          | (v2_struct_0 @ X15))),
% 0.75/0.98      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.75/0.98  thf('98', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.75/0.98          | (v2_struct_0 @ sk_A)
% 0.75/0.98          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98          | ~ (v1_funct_1 @ X0)
% 0.75/0.98          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.75/0.98          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))
% 0.75/0.98          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['96', '97'])).
% 0.75/0.98  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('101', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('102', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('103', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.75/0.98          | (v2_struct_0 @ sk_A)
% 0.75/0.98          | ~ (v1_funct_1 @ X0)
% 0.75/0.98          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.98          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.75/0.98  thf('104', plain,
% 0.75/0.98      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.75/0.98          = (u1_struct_0 @ sk_B))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['95', '103'])).
% 0.75/0.98  thf('105', plain,
% 0.75/0.98      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('106', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['75', '76'])).
% 0.75/0.98  thf('107', plain,
% 0.75/0.98      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.75/0.98          = (u1_struct_0 @ sk_B))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.75/0.98  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('109', plain,
% 0.75/0.98      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.75/0.98            = (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['107', '108'])).
% 0.75/0.98  thf('110', plain,
% 0.75/0.98      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.75/0.98            = (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['107', '108'])).
% 0.75/0.98  thf('111', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.98         (~ (m1_pre_topc @ X14 @ X15)
% 0.75/0.98          | ~ (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 0.75/0.98               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 0.75/0.98               (u1_struct_0 @ (k6_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15))) @ 
% 0.75/0.98               X16 @ (k7_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15)))
% 0.75/0.98          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 0.75/0.98          | ~ (m1_subset_1 @ X16 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.75/0.98                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.75/0.98          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 0.75/0.98               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.75/0.98          | ~ (v1_funct_1 @ X16)
% 0.75/0.98          | ~ (l1_pre_topc @ X15)
% 0.75/0.98          | ~ (v2_pre_topc @ X15)
% 0.75/0.98          | (v2_struct_0 @ X15))),
% 0.75/0.98      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.75/0.98  thf('112', plain,
% 0.75/0.98      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98           (k7_tmap_1 @ sk_A @ 
% 0.75/0.98            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.75/0.98        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['110', '111'])).
% 0.75/0.98  thf('113', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('114', plain,
% 0.75/0.98      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('115', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('118', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['75', '76'])).
% 0.75/0.98  thf('119', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('120', plain,
% 0.75/0.98      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('121', plain,
% 0.75/0.98      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('clc', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('122', plain,
% 0.75/0.98      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('clc', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf('123', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('124', plain,
% 0.75/0.98      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98           (k7_tmap_1 @ sk_A @ 
% 0.75/0.98            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | (v2_struct_0 @ sk_A)
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('demod', [status(thm)],
% 0.75/0.98                ['112', '113', '114', '115', '116', '117', '118', '119', 
% 0.75/0.98                 '120', '121', '122', '123'])).
% 0.75/0.98  thf('125', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_A)
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (k7_tmap_1 @ sk_A @ 
% 0.75/0.98              (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['124'])).
% 0.75/0.98  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('127', plain,
% 0.75/0.98      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98           (k7_tmap_1 @ sk_A @ 
% 0.75/0.98            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['125', '126'])).
% 0.75/0.98  thf('128', plain,
% 0.75/0.98      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['109', '127'])).
% 0.75/0.98  thf('129', plain,
% 0.75/0.98      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('130', plain,
% 0.75/0.98      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98           (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('demod', [status(thm)], ['128', '129'])).
% 0.75/0.98  thf('131', plain,
% 0.75/0.98      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.75/0.98        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.98             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/0.98             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['130'])).
% 0.75/0.98  thf('132', plain,
% 0.75/0.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.75/0.98        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['94', '131'])).
% 0.75/0.98  thf('133', plain,
% 0.75/0.98      (~ (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.75/0.98          sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('134', plain,
% 0.75/0.98      ((~ (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.75/0.98           sk_C)
% 0.75/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['132', '133'])).
% 0.75/0.98  thf('135', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('136', plain,
% 0.75/0.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf(t110_tmap_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.75/0.98               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.75/0.98                 ( ![D:$i]:
% 0.75/0.98                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.75/0.98                     ( r1_tmap_1 @
% 0.75/0.98                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.75/0.98                       ( k2_tmap_1 @
% 0.75/0.98                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.75/0.98                       D ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('137', plain,
% 0.75/0.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.75/0.98          | ((u1_struct_0 @ X24) != (X22))
% 0.75/0.98          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.75/0.98          | (r1_tmap_1 @ X24 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.75/0.98             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.75/0.98              (k7_tmap_1 @ X23 @ X22) @ X24) @ 
% 0.75/0.98             X25)
% 0.75/0.98          | ~ (m1_pre_topc @ X24 @ X23)
% 0.75/0.98          | (v2_struct_0 @ X24)
% 0.75/0.98          | ~ (l1_pre_topc @ X23)
% 0.75/0.98          | ~ (v2_pre_topc @ X23)
% 0.75/0.98          | (v2_struct_0 @ X23))),
% 0.75/0.98      inference('cnf', [status(esa)], [t110_tmap_1])).
% 0.75/0.98  thf('138', plain,
% 0.75/0.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.98         ((v2_struct_0 @ X23)
% 0.75/0.98          | ~ (v2_pre_topc @ X23)
% 0.75/0.98          | ~ (l1_pre_topc @ X23)
% 0.75/0.98          | (v2_struct_0 @ X24)
% 0.75/0.98          | ~ (m1_pre_topc @ X24 @ X23)
% 0.75/0.98          | (r1_tmap_1 @ X24 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.75/0.98             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.75/0.98              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24) @ 
% 0.75/0.98             X25)
% 0.75/0.98          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.75/0.98          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.75/0.98               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['137'])).
% 0.75/0.98  thf('139', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.75/0.98          | (r1_tmap_1 @ sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.75/0.98             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.75/0.98              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.75/0.98             X0)
% 0.75/0.98          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.75/0.98          | (v2_struct_0 @ sk_B)
% 0.75/0.98          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.98          | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['136', '138'])).
% 0.75/0.98  thf('140', plain,
% 0.75/0.98      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('141', plain,
% 0.75/0.98      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.75/0.98      inference('clc', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('142', plain,
% 0.75/0.98      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.75/0.98         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('143', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('146', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.75/0.98          | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98              (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.75/0.98             X0)
% 0.75/0.98          | (v2_struct_0 @ sk_B)
% 0.75/0.98          | (v2_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)],
% 0.75/0.98                ['139', '140', '141', '142', '143', '144', '145'])).
% 0.75/0.98  thf('147', plain,
% 0.75/0.98      (((v2_struct_0 @ sk_A)
% 0.75/0.98        | (v2_struct_0 @ sk_B)
% 0.75/0.98        | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.75/0.98           sk_C))),
% 0.75/0.98      inference('sup-', [status(thm)], ['135', '146'])).
% 0.75/0.98  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('149', plain,
% 0.75/0.98      (((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.75/0.98         sk_C)
% 0.75/0.98        | (v2_struct_0 @ sk_B))),
% 0.75/0.98      inference('clc', [status(thm)], ['147', '148'])).
% 0.75/0.98  thf('150', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('151', plain,
% 0.75/0.98      ((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.75/0.98         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.75/0.98        sk_C)),
% 0.75/0.98      inference('clc', [status(thm)], ['149', '150'])).
% 0.75/0.98  thf('152', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['134', '151'])).
% 0.75/0.98  thf(fc2_struct_0, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.75/0.98       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.75/0.98  thf('153', plain,
% 0.75/0.98      (![X1 : $i]:
% 0.75/0.98         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.75/0.98          | ~ (l1_struct_0 @ X1)
% 0.75/0.98          | (v2_struct_0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.75/0.98  thf('154', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['152', '153'])).
% 0.75/0.98  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(dt_l1_pre_topc, axiom,
% 0.75/0.98    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.75/0.98  thf('156', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.98  thf('157', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.98      inference('sup-', [status(thm)], ['155', '156'])).
% 0.75/0.98  thf('158', plain, ((v2_struct_0 @ sk_A)),
% 0.75/0.98      inference('demod', [status(thm)], ['154', '157'])).
% 0.75/0.98  thf('159', plain, ($false), inference('demod', [status(thm)], ['0', '158'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
