%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.02HOfhRN8H

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 838 expanded)
%              Number of leaves         :   28 ( 258 expanded)
%              Depth                    :   16
%              Number of atoms          : 2599 (16287 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(r5_binop_1_type,type,(
    r5_binop_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r4_binop_1_type,type,(
    r4_binop_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r6_binop_1_type,type,(
    r6_binop_1: $i > $i > $i > $o )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ~ ( m2_filter_1 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v8_relat_2 @ X7 )
      | ~ ( v3_relat_2 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X8 @ X7 ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_funct_2 @ X12 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m2_filter_1 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_funct_1 @ X12 )
      | ~ ( m2_filter_1 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('24',plain,
    ( ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('26',plain,
    ( ( v1_funct_1 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['14','21','28'])).

thf('30',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ~ ( m2_filter_1 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v8_relat_2 @ X7 )
      | ~ ( v3_relat_2 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X8 @ X7 ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_funct_2 @ X12 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m2_filter_1 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('49',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_funct_1 @ X12 )
      | ~ ( m2_filter_1 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('56',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('58',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','53','60'])).

thf('62',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','61'])).

thf('63',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

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

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r4_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( r5_binop_1 @ X5 @ X6 @ X4 )
      | ( r6_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_binop_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) )
      | ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v8_relat_2 @ X7 )
      | ~ ( v3_relat_2 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X8 @ X7 @ X9 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X8 @ X7 ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v8_relat_2 @ X7 )
      | ~ ( v3_relat_2 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) )
      | ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['70','84','98'])).

thf('100',plain,
    ( ~ ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ( r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','99'])).

thf('101',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
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

thf('104',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v3_relat_2 @ X17 )
      | ~ ( v8_relat_2 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m2_filter_1 @ X19 @ X18 @ X17 )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ X18 @ X17 ) @ ( k3_filter_1 @ X18 @ X17 @ X20 ) @ ( k3_filter_1 @ X18 @ X17 @ X19 ) )
      | ~ ( r4_binop_1 @ X18 @ X20 @ X19 )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X17 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_filter_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r4_binop_1 @ sk_A @ X0 @ X1 )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r4_binop_1 @ sk_A @ X0 @ X1 )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r4_binop_1 @ sk_A @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r4_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['101','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('114',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r6_binop_1 @ X5 @ X6 @ X4 )
      | ( r4_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_binop_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r4_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r4_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ~ ( r6_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r4_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    r6_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['26','27'])).

thf('123',plain,(
    r4_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r4_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m2_filter_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
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

thf('130',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v3_relat_2 @ X13 )
      | ~ ( v8_relat_2 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) )
      | ~ ( m2_filter_1 @ X15 @ X14 @ X13 )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ X14 @ X13 ) @ ( k3_filter_1 @ X14 @ X13 @ X16 ) @ ( k3_filter_1 @ X14 @ X13 @ X15 ) )
      | ~ ( r5_binop_1 @ X14 @ X16 @ X15 )
      | ~ ( m2_filter_1 @ X16 @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_filter_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r5_binop_1 @ sk_A @ X0 @ X1 )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ~ ( r5_binop_1 @ sk_A @ X0 @ X1 )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B )
      | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r5_binop_1 @ sk_A @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r5_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['127','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('139',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('140',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( r6_binop_1 @ X5 @ X6 @ X4 )
      | ( r5_binop_1 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_binop_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r5_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( r5_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r6_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ~ ( r6_binop_1 @ sk_A @ sk_C @ sk_D )
    | ( r5_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,(
    r6_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['26','27'])).

thf('149',plain,(
    r5_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['137','149'])).

thf('151',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    r5_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('155',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v8_relat_2 @ X7 )
      | ~ ( v3_relat_2 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X8 @ X7 @ X9 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X8 @ X7 ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) @ ( k8_eqrel_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['26','27'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','159'])).

thf('161',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('169',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v8_relat_2 @ X7 )
      | ~ ( v3_relat_2 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) @ X8 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(clc,[status(thm)],['26','27'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_C ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    r6_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['100','126','152','166','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['0','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.02HOfhRN8H
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 95 iterations in 0.055s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_filter_1_type, type, k3_filter_1: $i > $i > $i > $i).
% 0.21/0.50  thf(r5_binop_1_type, type, r5_binop_1: $i > $i > $i > $o).
% 0.21/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.21/0.50  thf(m2_filter_1_type, type, m2_filter_1: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.50  thf(r4_binop_1_type, type, r4_binop_1: $i > $i > $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(r6_binop_1_type, type, r6_binop_1: $i > $i > $i > $o).
% 0.21/0.50  thf(k8_eqrel_1_type, type, k8_eqrel_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(t11_filter_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.50             ( v8_relat_2 @ B ) & 
% 0.21/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.50                   ( ( r6_binop_1 @ A @ C @ D ) =>
% 0.21/0.50                     ( r6_binop_1 @
% 0.21/0.50                       ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.50                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.50                ( v8_relat_2 @ B ) & 
% 0.21/0.50                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.50                      ( ( r6_binop_1 @ A @ C @ D ) =>
% 0.21/0.50                        ( r6_binop_1 @
% 0.21/0.50                          ( k8_eqrel_1 @ A @ B ) @ 
% 0.21/0.50                          ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.50                          ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t11_filter_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (~ (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.50          (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m2_filter_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.21/0.50           ( ( v1_funct_1 @ C ) & 
% 0.21/0.50             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.50             ( m1_subset_1 @
% 0.21/0.50               C @ 
% 0.21/0.50               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X10)
% 0.21/0.50          | ~ (v1_relat_1 @ X11)
% 0.21/0.50          | (m1_subset_1 @ X12 @ 
% 0.21/0.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 0.21/0.50          | ~ (m2_filter_1 @ X12 @ X10 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_C @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | (v1_xboole_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.50          | (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_C @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.50        | (v1_xboole_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.50  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf(dt_k3_filter_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_partfun1 @ B @ A ) & 
% 0.21/0.50         ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.50         ( v1_funct_1 @ C ) & 
% 0.21/0.50         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.50         ( m1_subset_1 @
% 0.21/0.50           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.21/0.50       ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) ) & 
% 0.21/0.50         ( v1_funct_2 @
% 0.21/0.50           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.50           ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.21/0.50           ( k8_eqrel_1 @ A @ B ) ) & 
% 0.21/0.50         ( m1_subset_1 @
% 0.21/0.50           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.50           ( k1_zfmisc_1 @
% 0.21/0.50             ( k2_zfmisc_1 @
% 0.21/0.50               ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.21/0.50               ( k8_eqrel_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.50          | ~ (v8_relat_2 @ X7)
% 0.21/0.50          | ~ (v3_relat_2 @ X7)
% 0.21/0.50          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.50          | (v1_xboole_0 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X9)
% 0.21/0.50          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 0.21/0.50          | (m1_subset_1 @ (k3_filter_1 @ X8 @ X7 @ X9) @ 
% 0.21/0.50             (k1_zfmisc_1 @ 
% 0.21/0.50              (k2_zfmisc_1 @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k8_eqrel_1 @ X8 @ X7) @ (k8_eqrel_1 @ X8 @ X7)) @ 
% 0.21/0.50               (k8_eqrel_1 @ X8 @ X7)))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ X0))))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | (v1_funct_2 @ X12 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 0.21/0.51          | ~ (m2_filter_1 @ X12 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | (v1_funct_1 @ X12)
% 0.21/0.51          | ~ (m2_filter_1 @ X12 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('26', plain, (((v1_funct_1 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ X0))))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '21', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '29'])).
% 0.21/0.51  thf('31', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.21/0.51  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51          (k8_eqrel_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | (m1_subset_1 @ X12 @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 0.21/0.51          | ~ (m2_filter_1 @ X12 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.51          | ~ (v8_relat_2 @ X7)
% 0.21/0.51          | ~ (v3_relat_2 @ X7)
% 0.21/0.51          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.51          | (v1_xboole_0 @ X8)
% 0.21/0.51          | ~ (v1_funct_1 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 0.21/0.51          | (m1_subset_1 @ (k3_filter_1 @ X8 @ X7 @ X9) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k8_eqrel_1 @ X8 @ X7) @ (k8_eqrel_1 @ X8 @ X7)) @ 
% 0.21/0.51               (k8_eqrel_1 @ X8 @ X7)))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ X0))))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | (v1_funct_2 @ X12 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 0.21/0.51          | ~ (m2_filter_1 @ X12 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | (v1_funct_1 @ X12)
% 0.21/0.51          | ~ (m2_filter_1 @ X12 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('58', plain, (((v1_funct_1 @ sk_D) | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ X0))))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '53', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '61'])).
% 0.21/0.51  thf('63', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('65', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.51  thf('67', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51          (k8_eqrel_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.51  thf(d11_binop_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ B ) & 
% 0.21/0.51         ( v1_funct_2 @ B @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.51             ( m1_subset_1 @
% 0.21/0.51               C @ 
% 0.21/0.51               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.21/0.51           ( ( r6_binop_1 @ A @ B @ C ) <=>
% 0.21/0.51             ( ( r4_binop_1 @ A @ B @ C ) & ( r5_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X4)
% 0.21/0.51          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 0.21/0.51          | ~ (r4_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | ~ (r5_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | (r6_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 0.21/0.51          | ~ (v1_funct_2 @ X6 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 0.21/0.51          | ~ (v1_funct_1 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d11_binop_1])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ 
% 0.21/0.51                 (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                  (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51                 (k8_eqrel_1 @ sk_A @ sk_B))))
% 0.21/0.51          | (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51          | ~ (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51          | ~ (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.51          | ~ (v8_relat_2 @ X7)
% 0.21/0.51          | ~ (v3_relat_2 @ X7)
% 0.21/0.51          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.51          | (v1_xboole_0 @ X8)
% 0.21/0.51          | ~ (v1_funct_1 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 0.21/0.51          | (v1_funct_2 @ (k3_filter_1 @ X8 @ X7 @ X9) @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ X8 @ X7) @ (k8_eqrel_1 @ X8 @ X7)) @ 
% 0.21/0.51             (k8_eqrel_1 @ X8 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.51  thf('75', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ X0))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '77'])).
% 0.21/0.51  thf('79', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('80', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('81', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.21/0.51  thf('83', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.51        (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51        (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.51          | ~ (v8_relat_2 @ X7)
% 0.21/0.51          | ~ (v3_relat_2 @ X7)
% 0.21/0.51          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.51          | (v1_xboole_0 @ X8)
% 0.21/0.51          | ~ (v1_funct_1 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 0.21/0.51          | (v1_funct_1 @ (k3_filter_1 @ X8 @ X7 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['85', '91'])).
% 0.21/0.51  thf('93', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('95', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.21/0.51  thf('97', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('98', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ 
% 0.21/0.51                 (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                  (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51                 (k8_eqrel_1 @ sk_A @ sk_B))))
% 0.21/0.51          | (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51          | ~ (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51          | ~ (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['70', '84', '98'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      ((~ (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51        | ~ (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51        | (r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51        | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (k8_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.51        | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '99'])).
% 0.21/0.51  thf('101', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('102', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t9_filter_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.51             ( v8_relat_2 @ B ) & 
% 0.21/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.51                   ( ( r4_binop_1 @ A @ C @ D ) =>
% 0.21/0.51                     ( r4_binop_1 @
% 0.21/0.51                       ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.51                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (v1_partfun1 @ X17 @ X18)
% 0.21/0.51          | ~ (v3_relat_2 @ X17)
% 0.21/0.51          | ~ (v8_relat_2 @ X17)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.21/0.51          | ~ (m2_filter_1 @ X19 @ X18 @ X17)
% 0.21/0.51          | (r4_binop_1 @ (k8_eqrel_1 @ X18 @ X17) @ 
% 0.21/0.51             (k3_filter_1 @ X18 @ X17 @ X20) @ (k3_filter_1 @ X18 @ X17 @ X19))
% 0.21/0.51          | ~ (r4_binop_1 @ X18 @ X20 @ X19)
% 0.21/0.51          | ~ (m2_filter_1 @ X20 @ X18 @ X17)
% 0.21/0.51          | (v1_xboole_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t9_filter_1])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (r4_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.51          | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (v8_relat_2 @ sk_B)
% 0.21/0.51          | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.51  thf('106', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('107', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('108', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (r4_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.51          | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X0))
% 0.21/0.51          | ~ (r4_binop_1 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['102', '109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (r4_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['101', '110'])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X4)
% 0.21/0.51          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 0.21/0.51          | ~ (r6_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | (r4_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 0.21/0.51          | ~ (v1_funct_2 @ X6 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 0.21/0.51          | ~ (v1_funct_1 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d11_binop_1])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.51          | (r4_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.51          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.51  thf('116', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.51          | (r4_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.51          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.21/0.51  thf('119', plain,
% 0.21/0.51      ((~ (r6_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | (r4_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['112', '118'])).
% 0.21/0.51  thf('120', plain, ((r6_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('121', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('123', plain, ((r4_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.21/0.51  thf('124', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['111', '123'])).
% 0.21/0.51  thf('125', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('126', plain,
% 0.21/0.51      ((r4_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['124', '125'])).
% 0.21/0.51  thf('127', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('128', plain, ((m2_filter_1 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('129', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t10_filter_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.51             ( v8_relat_2 @ B ) & 
% 0.21/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.51                   ( ( r5_binop_1 @ A @ C @ D ) =>
% 0.21/0.51                     ( r5_binop_1 @
% 0.21/0.51                       ( k8_eqrel_1 @ A @ B ) @ ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.51                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('130', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (v1_partfun1 @ X13 @ X14)
% 0.21/0.51          | ~ (v3_relat_2 @ X13)
% 0.21/0.51          | ~ (v8_relat_2 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.21/0.51          | ~ (m2_filter_1 @ X15 @ X14 @ X13)
% 0.21/0.51          | (r5_binop_1 @ (k8_eqrel_1 @ X14 @ X13) @ 
% 0.21/0.51             (k3_filter_1 @ X14 @ X13 @ X16) @ (k3_filter_1 @ X14 @ X13 @ X15))
% 0.21/0.51          | ~ (r5_binop_1 @ X14 @ X16 @ X15)
% 0.21/0.51          | ~ (m2_filter_1 @ X16 @ X14 @ X13)
% 0.21/0.51          | (v1_xboole_0 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_filter_1])).
% 0.21/0.51  thf('131', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (r5_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.51          | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (v8_relat_2 @ sk_B)
% 0.21/0.51          | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['129', '130'])).
% 0.21/0.51  thf('132', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('133', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('134', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('135', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (r5_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.51          | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.21/0.51  thf('136', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m2_filter_1 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51             (k3_filter_1 @ sk_A @ sk_B @ X0))
% 0.21/0.51          | ~ (r5_binop_1 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['128', '135'])).
% 0.21/0.51  thf('137', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (r5_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['127', '136'])).
% 0.21/0.51  thf('138', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('139', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('140', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X4)
% 0.21/0.51          | ~ (v1_funct_2 @ X4 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 0.21/0.51          | ~ (r6_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | (r5_binop_1 @ X5 @ X6 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)))
% 0.21/0.51          | ~ (v1_funct_2 @ X6 @ (k2_zfmisc_1 @ X5 @ X5) @ X5)
% 0.21/0.51          | ~ (v1_funct_1 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d11_binop_1])).
% 0.21/0.51  thf('141', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.51          | (r5_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.51          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['139', '140'])).
% 0.21/0.51  thf('142', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('144', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.51          | (r5_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.51          | ~ (r6_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.21/0.51  thf('145', plain,
% 0.21/0.51      ((~ (r6_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | (r5_binop_1 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['138', '144'])).
% 0.21/0.51  thf('146', plain, ((r6_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('147', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('149', plain, ((r5_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.21/0.51  thf('150', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['137', '149'])).
% 0.21/0.51  thf('151', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('152', plain,
% 0.21/0.51      ((r5_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['150', '151'])).
% 0.21/0.51  thf('153', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('154', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('155', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.51          | ~ (v8_relat_2 @ X7)
% 0.21/0.51          | ~ (v3_relat_2 @ X7)
% 0.21/0.51          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.51          | (v1_xboole_0 @ X8)
% 0.21/0.51          | ~ (v1_funct_1 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 0.21/0.51          | (v1_funct_2 @ (k3_filter_1 @ X8 @ X7 @ X9) @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ X8 @ X7) @ (k8_eqrel_1 @ X8 @ X7)) @ 
% 0.21/0.51             (k8_eqrel_1 @ X8 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.51  thf('156', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['154', '155'])).
% 0.21/0.51  thf('157', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('159', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ X0))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.21/0.51  thf('160', plain,
% 0.21/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['153', '159'])).
% 0.21/0.51  thf('161', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('162', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('163', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('164', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 0.21/0.51  thf('165', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('166', plain,
% 0.21/0.51      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.51        (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51        (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['164', '165'])).
% 0.21/0.51  thf('167', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('168', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('169', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.51          | ~ (v8_relat_2 @ X7)
% 0.21/0.51          | ~ (v3_relat_2 @ X7)
% 0.21/0.51          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.51          | (v1_xboole_0 @ X8)
% 0.21/0.51          | ~ (v1_funct_1 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8) @ X8)))
% 0.21/0.51          | (v1_funct_1 @ (k3_filter_1 @ X8 @ X7 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.51  thf('170', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['168', '169'])).
% 0.21/0.51  thf('171', plain, ((v1_funct_2 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('173', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_C))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v3_relat_2 @ X0)
% 0.21/0.51          | ~ (v8_relat_2 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['170', '171', '172'])).
% 0.21/0.51  thf('174', plain,
% 0.21/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['167', '173'])).
% 0.21/0.51  thf('175', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('176', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('177', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('178', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 0.21/0.51  thf('179', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('180', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['178', '179'])).
% 0.21/0.51  thf('181', plain,
% 0.21/0.51      ((r6_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k3_filter_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['100', '126', '152', '166', '180'])).
% 0.21/0.51  thf('182', plain, ($false), inference('demod', [status(thm)], ['0', '181'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
