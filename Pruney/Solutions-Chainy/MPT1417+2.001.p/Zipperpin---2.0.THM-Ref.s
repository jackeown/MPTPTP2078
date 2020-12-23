%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UjkDhiFlu9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 748 expanded)
%              Number of leaves         :   27 ( 228 expanded)
%              Depth                    :   15
%              Number of atoms          : 2585 (15867 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r4_binop_1_type,type,(
    r4_binop_1: $i > $i > $i > $o )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r5_binop_1_type,type,(
    r5_binop_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r6_binop_1_type,type,(
    r6_binop_1: $i > $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t11_filter_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m2_filter_1 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r6_binop_1 @ A @ C @ D )
                   => ( r6_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_partfun1 @ B @ A )
              & ( v3_relat_2 @ B )
              & ( v8_relat_2 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( m2_filter_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_filter_1 @ D @ A @ B )
                   => ( ( r6_binop_1 @ A @ C @ D )
                     => ( r6_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_filter_1])).

thf('0',plain,(
    ~ ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( m2_filter_1 @ C @ A @ B )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 ) ) )
      | ~ ( m2_filter_1 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(dt_k3_filter_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_partfun1 @ B @ A )
        & ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k3_filter_1 @ A @ B @ C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ ( k8_eqrel_1 @ A @ B ) )
        & ( m1_subset_1 @ ( k3_filter_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ ( k8_eqrel_1 @ A @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_2 @ X11 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 )
      | ~ ( m2_filter_1 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_1 @ X11 )
      | ~ ( m2_filter_1 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('22',plain,
    ( ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,
    ( ( v1_funct_1 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','19','26'])).

thf('28',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 ) ) )
      | ~ ( m2_filter_1 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_2 @ X11 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 )
      | ~ ( m2_filter_1 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('47',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('49',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_funct_1 @ X11 )
      | ~ ( m2_filter_1 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('54',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('56',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','51','58'])).

thf('60',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['35','59'])).

thf('61',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf(d11_binop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
         => ( ( r6_binop_1 @ A @ B @ C )
          <=> ( ( r4_binop_1 @ A @ B @ C )
              & ( r5_binop_1 @ A @ B @ C ) ) ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 ) ) )
      | ~ ( r4_binop_1 @ X4 @ X5 @ X3 )
      | ~ ( r5_binop_1 @ X4 @ X5 @ X3 )
      | ( r6_binop_1 @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_binop_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) )
      | ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('71',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['49','50'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['56','57'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('85',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['49','50'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['56','57'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) )
      | ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['68','82','96'])).

thf('98',plain,
    ( ~ ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','97'])).

thf('99',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m2_filter_1 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r4_binop_1 @ A @ C @ D )
                   => ( r4_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v3_relat_2 @ X16 )
      | ~ ( v8_relat_2 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m2_filter_1 @ X18 @ X17 @ X16 )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ X17 @ X16 ) @ ( k3_filter_1 @ X17 @ X16 @ X19 ) @ ( k3_filter_1 @ X17 @ X16 @ X18 ) )
      | ~ ( r4_binop_1 @ X17 @ X19 @ X18 )
      | ~ ( m2_filter_1 @ X19 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_filter_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r4_binop_1 @ sk_A @ X0 @ X1 )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r4_binop_1 @ sk_A @ X0 @ X1 )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r4_binop_1 @ sk_A @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r4_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('112',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 ) ) )
      | ~ ( r6_binop_1 @ X4 @ X5 @ X3 )
      | ( r4_binop_1 @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_binop_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r4_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['49','50'])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['56','57'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r4_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ~ ( r6_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r4_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    r6_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf('121',plain,(
    r4_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m2_filter_1 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r5_binop_1 @ A @ C @ D )
                   => ( r5_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v3_relat_2 @ X12 )
      | ~ ( v8_relat_2 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) )
      | ~ ( m2_filter_1 @ X14 @ X13 @ X12 )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ X13 @ X12 ) @ ( k3_filter_1 @ X13 @ X12 @ X15 ) @ ( k3_filter_1 @ X13 @ X12 @ X14 ) )
      | ~ ( r5_binop_1 @ X13 @ X15 @ X14 )
      | ~ ( m2_filter_1 @ X15 @ X13 @ X12 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t10_filter_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r5_binop_1 @ sk_A @ X0 @ X1 )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r5_binop_1 @ sk_A @ X0 @ X1 )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r5_binop_1 @ sk_A @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r5_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['125','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('137',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('138',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 ) ) )
      | ~ ( r6_binop_1 @ X4 @ X5 @ X3 )
      | ( r5_binop_1 @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X4 @ X4 ) @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_binop_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r5_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['49','50'])).

thf('141',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['56','57'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r5_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ~ ( r6_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r5_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','142'])).

thf('144',plain,(
    r6_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf('147',plain,(
    r5_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['135','147'])).

thf('149',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('153',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','157'])).

thf('159',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('167',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','171'])).

thf('173',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['98','124','150','164','178'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['0','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UjkDhiFlu9
% 0.13/0.36  % Computer   : n021.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:46:49 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 95 iterations in 0.072s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.55  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(r4_binop_1_type, type, r4_binop_1: $i > $i > $i > $o).
% 0.22/0.55  thf(k3_filter_1_type, type, k3_filter_1: $i > $i > $i > $i).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(r5_binop_1_type, type, r5_binop_1: $i > $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(r6_binop_1_type, type, r6_binop_1: $i > $i > $i > $o).
% 0.22/0.55  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(m2_filter_1_type, type, m2_filter_1: $i > $i > $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(k8_eqrel_1_type, type, k8_eqrel_1: $i > $i > $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(t11_filter_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.55             ( v8_relat_2 @ B ) & 
% 0.22/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.55                   ( ( r6_binop_1 @ A @ C @ D ) =>
% 0.22/0.55                     ( r6_binop_1 @
% 0.22/0.55                       ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.55                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.55                ( v8_relat_2 @ B ) & 
% 0.22/0.55                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.22/0.55                  ( ![D:$i]:
% 0.22/0.55                    ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.55                      ( ( r6_binop_1 @ A @ C @ D ) =>
% 0.22/0.55                        ( r6_binop_1 @
% 0.22/0.55                          ( k8_eqrel_1 @ A @ B ) @ 
% 0.22/0.55                          ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.55                          ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t11_filter_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (~ (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55          (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('2', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_m2_filter_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.22/0.55           ( ( v1_funct_1 @ C ) & 
% 0.22/0.55             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               C @ 
% 0.22/0.55               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X10)
% 0.22/0.55          | (m1_subset_1 @ X11 @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X9) @ X9)))
% 0.22/0.55          | ~ (m2_filter_1 @ X11 @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_C @ 
% 0.22/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(cc1_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( v1_relat_1 @ C ) ))).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((v1_relat_1 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.55  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_C @ 
% 0.22/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.55  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf(dt_k3_filter_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_partfun1 @ B @ A ) & 
% 0.22/0.55         ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.55         ( v1_funct_1 @ C ) & 
% 0.22/0.55         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.55         ( m1_subset_1 @
% 0.22/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.22/0.55       ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) ) & 
% 0.22/0.55         ( v1_funct_2 @
% 0.22/0.55           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.55           ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.22/0.55           ( k8_eqrel_1 @ A @ B ) ) & 
% 0.22/0.55         ( m1_subset_1 @
% 0.22/0.55           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.55           ( k1_zfmisc_1 @
% 0.22/0.55             ( k2_zfmisc_1 @
% 0.22/0.55               ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.22/0.55               ( k8_eqrel_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7)))
% 0.22/0.55          | ~ (v8_relat_2 @ X6)
% 0.22/0.55          | ~ (v3_relat_2 @ X6)
% 0.22/0.55          | ~ (v1_partfun1 @ X6 @ X7)
% 0.22/0.55          | (v1_xboole_0 @ X7)
% 0.22/0.55          | ~ (v1_funct_1 @ X8)
% 0.22/0.55          | ~ (v1_funct_2 @ X8 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)))
% 0.22/0.55          | (m1_subset_1 @ (k3_filter_1 @ X7 @ X6 @ X8) @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ 
% 0.22/0.55               (k2_zfmisc_1 @ (k8_eqrel_1 @ X7 @ X6) @ (k8_eqrel_1 @ X7 @ X6)) @ 
% 0.22/0.55               (k8_eqrel_1 @ X7 @ X6)))))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ X0))))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X10)
% 0.22/0.55          | (v1_funct_2 @ X11 @ (k2_zfmisc_1 @ X9 @ X9) @ X9)
% 0.22/0.55          | ~ (m2_filter_1 @ X11 @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.55  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('19', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('20', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X10)
% 0.22/0.55          | (v1_funct_1 @ X11)
% 0.22/0.55          | ~ (m2_filter_1 @ X11 @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (((v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('24', plain, (((v1_funct_1 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('25', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ X0))))
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['12', '19', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A)
% 0.22/0.55        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '27'])).
% 0.22/0.55  thf('29', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('30', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('31', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.22/0.55  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ 
% 0.22/0.55          (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55          (k8_eqrel_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('36', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X10)
% 0.22/0.55          | (m1_subset_1 @ X11 @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X9) @ X9)))
% 0.22/0.55          | ~ (m2_filter_1 @ X11 @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_D @ 
% 0.22/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.55  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_D @ 
% 0.22/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7)))
% 0.22/0.55          | ~ (v8_relat_2 @ X6)
% 0.22/0.55          | ~ (v3_relat_2 @ X6)
% 0.22/0.55          | ~ (v1_partfun1 @ X6 @ X7)
% 0.22/0.55          | (v1_xboole_0 @ X7)
% 0.22/0.55          | ~ (v1_funct_1 @ X8)
% 0.22/0.55          | ~ (v1_funct_2 @ X8 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)))
% 0.22/0.55          | (m1_subset_1 @ (k3_filter_1 @ X7 @ X6 @ X8) @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ 
% 0.22/0.55               (k2_zfmisc_1 @ (k8_eqrel_1 @ X7 @ X6) @ (k8_eqrel_1 @ X7 @ X6)) @ 
% 0.22/0.55               (k8_eqrel_1 @ X7 @ X6)))))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ X0))))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.55  thf('45', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X10)
% 0.22/0.55          | (v1_funct_2 @ X11 @ (k2_zfmisc_1 @ X9 @ X9) @ X9)
% 0.22/0.55          | ~ (m2_filter_1 @ X11 @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.55  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('52', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X10)
% 0.22/0.55          | (v1_funct_1 @ X11)
% 0.22/0.55          | ~ (m2_filter_1 @ X11 @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (((v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('56', plain, (((v1_funct_1 @ sk_D) | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ X0))))
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['44', '51', '58'])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A)
% 0.22/0.55        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['35', '59'])).
% 0.22/0.55  thf('61', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('63', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.22/0.55  thf('65', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ 
% 0.22/0.55          (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55          (k8_eqrel_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('clc', [status(thm)], ['64', '65'])).
% 0.22/0.55  thf(d11_binop_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ B ) & 
% 0.22/0.55         ( v1_funct_2 @ B @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.55         ( m1_subset_1 @
% 0.22/0.55           B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.55             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               C @ 
% 0.22/0.55               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.22/0.55           ( ( r6_binop_1 @ A @ B @ C ) <=>
% 0.22/0.55             ( ( r4_binop_1 @ A @ B @ C ) & ( r5_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X3)
% 0.22/0.55          | ~ (v1_funct_2 @ X3 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)
% 0.22/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)))
% 0.22/0.55          | ~ (r4_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | ~ (r5_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | (r6_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)))
% 0.22/0.55          | ~ (v1_funct_2 @ X5 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)
% 0.22/0.55          | ~ (v1_funct_1 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [d11_binop_1])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ 
% 0.22/0.55               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ 
% 0.22/0.55                 (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55                  (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55                 (k8_eqrel_1 @ sk_A @ sk_B))))
% 0.22/0.55          | (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55          | ~ (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.55               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55          | ~ (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.55               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.55          | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7)))
% 0.22/0.55          | ~ (v8_relat_2 @ X6)
% 0.22/0.55          | ~ (v3_relat_2 @ X6)
% 0.22/0.55          | ~ (v1_partfun1 @ X6 @ X7)
% 0.22/0.55          | (v1_xboole_0 @ X7)
% 0.22/0.55          | ~ (v1_funct_1 @ X8)
% 0.22/0.55          | ~ (v1_funct_2 @ X8 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)))
% 0.22/0.55          | (v1_funct_2 @ (k3_filter_1 @ X7 @ X6 @ X8) @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ X7 @ X6) @ (k8_eqrel_1 @ X7 @ X6)) @ 
% 0.22/0.55             (k8_eqrel_1 @ X7 @ X6)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ X0))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.55  thf('73', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ X0))
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['69', '75'])).
% 0.22/0.55  thf('77', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('78', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('79', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.22/0.55  thf('81', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.55        (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55        (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['80', '81'])).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('84', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('85', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7)))
% 0.22/0.55          | ~ (v8_relat_2 @ X6)
% 0.22/0.55          | ~ (v3_relat_2 @ X6)
% 0.22/0.55          | ~ (v1_partfun1 @ X6 @ X7)
% 0.22/0.55          | (v1_xboole_0 @ X7)
% 0.22/0.55          | ~ (v1_funct_1 @ X8)
% 0.22/0.55          | ~ (v1_funct_2 @ X8 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)))
% 0.22/0.55          | (v1_funct_1 @ (k3_filter_1 @ X7 @ X6 @ X8)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.55  thf('86', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.22/0.55  thf('87', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['83', '89'])).
% 0.22/0.55  thf('91', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('92', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('93', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('94', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.22/0.55  thf('95', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('96', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.55      inference('clc', [status(thm)], ['94', '95'])).
% 0.22/0.55  thf('97', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ 
% 0.22/0.55               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ 
% 0.22/0.55                 (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55                  (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55                 (k8_eqrel_1 @ sk_A @ sk_B))))
% 0.22/0.55          | (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55          | ~ (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.55               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55          | ~ (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.55               (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('demod', [status(thm)], ['68', '82', '96'])).
% 0.22/0.55  thf('98', plain,
% 0.22/0.55      ((~ (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55        | ~ (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55        | (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.55        | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55             (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.55        | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['34', '97'])).
% 0.22/0.55  thf('99', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('100', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('101', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t9_filter_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.55             ( v8_relat_2 @ B ) & 
% 0.22/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.55                   ( ( r4_binop_1 @ A @ C @ D ) =>
% 0.22/0.55                     ( r4_binop_1 @
% 0.22/0.55                       ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.55                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('102', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.55         (~ (v1_partfun1 @ X16 @ X17)
% 0.22/0.55          | ~ (v3_relat_2 @ X16)
% 0.22/0.55          | ~ (v8_relat_2 @ X16)
% 0.22/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.22/0.55          | ~ (m2_filter_1 @ X18 @ X17 @ X16)
% 0.22/0.55          | (r4_binop_1 @ (k8_eqrel_1 @ X17 @ X16) @ 
% 0.22/0.55             (k3_filter_1 @ X17 @ X16 @ X19) @ (k3_filter_1 @ X17 @ X16 @ X18))
% 0.22/0.55          | ~ (r4_binop_1 @ X17 @ X19 @ X18)
% 0.22/0.55          | ~ (m2_filter_1 @ X19 @ X17 @ X16)
% 0.22/0.55          | (v1_xboole_0 @ X17))),
% 0.22/0.55      inference('cnf', [status(esa)], [t9_filter_1])).
% 0.22/0.55  thf('103', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.22/0.55          | ~ (r4_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.55          | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.55          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.22/0.55          | ~ (v8_relat_2 @ sk_B)
% 0.22/0.55          | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.55  thf('104', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('105', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('106', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('107', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.22/0.55          | ~ (r4_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.55          | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.55          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.22/0.55  thf('108', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.22/0.55          | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X0))
% 0.22/0.55          | ~ (r4_binop_1 @ sk_A @ sk_C @ X0)
% 0.22/0.55          | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['100', '107'])).
% 0.22/0.55  thf('109', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | ~ (r4_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.22/0.55        | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['99', '108'])).
% 0.22/0.55  thf('110', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('111', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('112', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X3)
% 0.22/0.55          | ~ (v1_funct_2 @ X3 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)
% 0.22/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)))
% 0.22/0.55          | ~ (r6_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | (r4_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)))
% 0.22/0.55          | ~ (v1_funct_2 @ X5 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)
% 0.22/0.55          | ~ (v1_funct_1 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [d11_binop_1])).
% 0.22/0.55  thf('113', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55          | (r4_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.55          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.22/0.55  thf('114', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('116', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55          | (r4_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.55          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.22/0.55  thf('117', plain,
% 0.22/0.55      ((~ (r6_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.22/0.55        | (r4_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.22/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['110', '116'])).
% 0.22/0.55  thf('118', plain, ((r6_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('119', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('121', plain, ((r4_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.55      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.22/0.55  thf('122', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('demod', [status(thm)], ['109', '121'])).
% 0.22/0.55  thf('123', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('124', plain,
% 0.22/0.55      ((r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55        (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.55      inference('clc', [status(thm)], ['122', '123'])).
% 0.22/0.55  thf('125', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('126', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('127', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t10_filter_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.55             ( v8_relat_2 @ B ) & 
% 0.22/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.55                   ( ( r5_binop_1 @ A @ C @ D ) =>
% 0.22/0.55                     ( r5_binop_1 @
% 0.22/0.55                       ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.55                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('128', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (v1_partfun1 @ X12 @ X13)
% 0.22/0.55          | ~ (v3_relat_2 @ X12)
% 0.22/0.55          | ~ (v8_relat_2 @ X12)
% 0.22/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))
% 0.22/0.55          | ~ (m2_filter_1 @ X14 @ X13 @ X12)
% 0.22/0.55          | (r5_binop_1 @ (k8_eqrel_1 @ X13 @ X12) @ 
% 0.22/0.55             (k3_filter_1 @ X13 @ X12 @ X15) @ (k3_filter_1 @ X13 @ X12 @ X14))
% 0.22/0.55          | ~ (r5_binop_1 @ X13 @ X15 @ X14)
% 0.22/0.55          | ~ (m2_filter_1 @ X15 @ X13 @ X12)
% 0.22/0.55          | (v1_xboole_0 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_filter_1])).
% 0.22/0.55  thf('129', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.22/0.55          | ~ (r5_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.55          | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.55          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.22/0.55          | ~ (v8_relat_2 @ sk_B)
% 0.22/0.55          | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['127', '128'])).
% 0.22/0.55  thf('130', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('131', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('132', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('133', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.22/0.55          | ~ (r5_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.55          | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.55          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.22/0.55  thf('134', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.22/0.55          | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55             (k3_filter_1 @ sk_A @ sk_B @ X0))
% 0.22/0.55          | ~ (r5_binop_1 @ sk_A @ sk_C @ X0)
% 0.22/0.55          | (v1_xboole_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['126', '133'])).
% 0.22/0.55  thf('135', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | ~ (r5_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.22/0.55        | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['125', '134'])).
% 0.22/0.55  thf('136', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('137', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('138', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X3)
% 0.22/0.55          | ~ (v1_funct_2 @ X3 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)
% 0.22/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)))
% 0.22/0.55          | ~ (r6_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | (r5_binop_1 @ X4 @ X5 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)))
% 0.22/0.55          | ~ (v1_funct_2 @ X5 @ (k2_zfmisc_1 @ X4 @ X4) @ X4)
% 0.22/0.55          | ~ (v1_funct_1 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [d11_binop_1])).
% 0.22/0.55  thf('139', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55          | (r5_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.55          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['137', '138'])).
% 0.22/0.55  thf('140', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('141', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('142', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.55          | (r5_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.55          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.22/0.55  thf('143', plain,
% 0.22/0.55      ((~ (r6_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.22/0.55        | (r5_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.22/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['136', '142'])).
% 0.22/0.55  thf('144', plain, ((r6_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('145', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('147', plain, ((r5_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.55      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.22/0.55  thf('148', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.55      inference('demod', [status(thm)], ['135', '147'])).
% 0.22/0.55  thf('149', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('150', plain,
% 0.22/0.55      ((r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55        (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.55      inference('clc', [status(thm)], ['148', '149'])).
% 0.22/0.55  thf('151', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('152', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('153', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7)))
% 0.22/0.55          | ~ (v8_relat_2 @ X6)
% 0.22/0.55          | ~ (v3_relat_2 @ X6)
% 0.22/0.55          | ~ (v1_partfun1 @ X6 @ X7)
% 0.22/0.55          | (v1_xboole_0 @ X7)
% 0.22/0.55          | ~ (v1_funct_1 @ X8)
% 0.22/0.55          | ~ (v1_funct_2 @ X8 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)))
% 0.22/0.55          | (v1_funct_2 @ (k3_filter_1 @ X7 @ X6 @ X8) @ 
% 0.22/0.55             (k2_zfmisc_1 @ (k8_eqrel_1 @ X7 @ X6) @ (k8_eqrel_1 @ X7 @ X6)) @ 
% 0.22/0.55             (k8_eqrel_1 @ X7 @ X6)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.55  thf('154', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ X0))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['152', '153'])).
% 0.22/0.55  thf('155', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('157', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ X0))
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.22/0.55  thf('158', plain,
% 0.22/0.55      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['151', '157'])).
% 0.22/0.55  thf('159', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('160', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('161', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('162', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 0.22/0.55  thf('163', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('164', plain,
% 0.22/0.55      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.55        (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.55        (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['162', '163'])).
% 0.22/0.55  thf('165', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('166', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('167', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7)))
% 0.22/0.55          | ~ (v8_relat_2 @ X6)
% 0.22/0.55          | ~ (v3_relat_2 @ X6)
% 0.22/0.55          | ~ (v1_partfun1 @ X6 @ X7)
% 0.22/0.55          | (v1_xboole_0 @ X7)
% 0.22/0.55          | ~ (v1_funct_1 @ X8)
% 0.22/0.55          | ~ (v1_funct_2 @ X8 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7) @ X7)))
% 0.22/0.55          | (v1_funct_1 @ (k3_filter_1 @ X7 @ X6 @ X8)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.55  thf('168', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['166', '167'])).
% 0.22/0.55  thf('169', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('171', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C))
% 0.22/0.55          | (v1_xboole_0 @ sk_A)
% 0.22/0.55          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.55          | ~ (v3_relat_2 @ X0)
% 0.22/0.55          | ~ (v8_relat_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.22/0.55  thf('172', plain,
% 0.22/0.55      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.55        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['165', '171'])).
% 0.22/0.55  thf('173', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('174', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('175', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('176', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_A)
% 0.22/0.55        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.55      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.22/0.55  thf('177', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('178', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.55      inference('clc', [status(thm)], ['176', '177'])).
% 0.22/0.55  thf('179', plain,
% 0.22/0.55      ((r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.55        (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['98', '124', '150', '164', '178'])).
% 0.22/0.55  thf('180', plain, ($false), inference('demod', [status(thm)], ['0', '179'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
