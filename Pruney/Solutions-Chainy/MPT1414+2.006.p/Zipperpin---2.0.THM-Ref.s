%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8IcTyNBqH0

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 790 expanded)
%              Number of leaves         :   39 ( 249 expanded)
%              Depth                    :   17
%              Number of atoms          : 2340 (16125 expanded)
%              Number of equality atoms :   15 (  48 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_eqrel_1_type,type,(
    m1_eqrel_1: $i > $i > $o )).

thf(k7_eqrel_1_type,type,(
    k7_eqrel_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t8_filter_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r3_binop_1 @ A @ C @ D )
                   => ( r3_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_partfun1 @ B @ A )
              & ( v3_relat_2 @ B )
              & ( v8_relat_2 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ! [D: $i] :
                    ( ( m2_filter_1 @ D @ A @ B )
                   => ( ( r3_binop_1 @ A @ C @ D )
                     => ( r3_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_filter_1])).

thf('0',plain,(
    ~ ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k8_eqrel_1 @ A @ B )
        = ( k7_eqrel_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k8_eqrel_1 @ X28 @ X29 )
        = ( k7_eqrel_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v1_partfun1 @ X29 @ X28 )
      | ~ ( v8_relat_2 @ X29 )
      | ~ ( v3_relat_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_eqrel_1])).

thf('3',plain,
    ( ~ ( v3_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( ( k8_eqrel_1 @ sk_A @ sk_B )
      = ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
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

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) @ X23 ) ) )
      | ~ ( m2_filter_1 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(d7_binop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
         => ( ( r3_binop_1 @ A @ B @ C )
          <=> ( ( r1_binop_1 @ A @ B @ C )
              & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r3_binop_1 @ X11 @ X12 @ X10 )
      | ( r2_binop_1 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_funct_2 @ X25 @ ( k2_zfmisc_1 @ X23 @ X23 ) @ X23 )
      | ~ ( m2_filter_1 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_funct_1 @ X25 )
      | ~ ( m2_filter_1 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('32',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('34',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','29','36'])).

thf('38',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['9','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r2_binop_1 @ A @ C @ D )
                   => ( r2_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_partfun1 @ X34 @ X35 )
      | ~ ( v3_relat_2 @ X34 )
      | ~ ( v8_relat_2 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( m2_filter_1 @ X36 @ X35 @ X34 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ X35 @ X34 ) @ ( k9_eqrel_1 @ X35 @ X34 @ X37 ) @ ( k3_filter_1 @ X35 @ X34 @ X36 ) )
      | ~ ( r2_binop_1 @ X35 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_filter_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('46',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

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

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) )
      | ~ ( v8_relat_2 @ X13 )
      | ~ ( v3_relat_2 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X14 @ X13 ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('68',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('69',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r1_binop_1 @ X11 @ X12 @ X10 )
      | ~ ( r2_binop_1 @ X11 @ X12 @ X10 )
      | ( r3_binop_1 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) )
      | ~ ( v8_relat_2 @ X13 )
      | ~ ( v3_relat_2 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) )
      | ~ ( v8_relat_2 @ X13 )
      | ~ ( v3_relat_2 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) @ X14 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X14 @ X13 @ X15 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X14 @ X13 ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('102',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('103',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['89','106'])).

thf('108',plain,
    ( ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','107'])).

thf('109',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('111',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r3_binop_1 @ X11 @ X12 @ X10 )
      | ( r1_binop_1 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('114',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r1_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r1_binop_1 @ A @ C @ D )
                   => ( r1_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X31 )
      | ~ ( v3_relat_2 @ X30 )
      | ~ ( v8_relat_2 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( m2_filter_1 @ X32 @ X31 @ X30 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ X31 @ X30 ) @ ( k9_eqrel_1 @ X31 @ X30 @ X33 ) @ ( k3_filter_1 @ X31 @ X30 @ X32 ) )
      | ~ ( r1_binop_1 @ X31 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('124',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['118','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_eqrel_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
        & ( m1_subset_1 @ C @ A ) )
     => ( m2_subset_1 @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) @ ( k8_eqrel_1 @ A @ B ) ) ) )).

thf('136',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v8_relat_2 @ X18 )
      | ~ ( v3_relat_2 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X19 @ X18 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) @ ( k8_eqrel_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('139',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['134','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( m1_eqrel_1 @ ( k8_eqrel_1 @ A @ B ) @ A ) ) )).

thf('147',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_eqrel_1 @ ( k8_eqrel_1 @ X16 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v8_relat_2 @ X17 )
      | ~ ( v3_relat_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_eqrel_1])).

thf('148',plain,
    ( ~ ( v3_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf(dt_m1_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_eqrel_1 @ B @ A )
     => ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('153',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) )
      | ~ ( m1_eqrel_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_eqrel_1])).

thf('154',plain,(
    m1_subset_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('156',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('157',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X9 @ X7 )
      | ~ ( m2_subset_1 @ X9 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','158'])).

thf('160',plain,(
    m1_subset_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('162',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('164',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ A @ B ) ) ) )).

thf('166',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v3_relat_2 @ X27 )
      | ~ ( v8_relat_2 @ X27 )
      | ~ ( v1_partfun1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_eqrel_1])).

thf('167',plain,
    ( ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['164','173'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['159','174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('177',plain,(
    m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['108','133','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['8','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8IcTyNBqH0
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:16:34 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 90 iterations in 0.045s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(r1_binop_1_type, type, r1_binop_1: $i > $i > $i > $o).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.23/0.52  thf(r3_binop_1_type, type, r3_binop_1: $i > $i > $i > $o).
% 0.23/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.52  thf(m1_eqrel_1_type, type, m1_eqrel_1: $i > $i > $o).
% 0.23/0.52  thf(k7_eqrel_1_type, type, k7_eqrel_1: $i > $i > $i).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.52  thf(r2_binop_1_type, type, r2_binop_1: $i > $i > $i > $o).
% 0.23/0.52  thf(k9_eqrel_1_type, type, k9_eqrel_1: $i > $i > $i > $i).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.52  thf(k3_filter_1_type, type, k3_filter_1: $i > $i > $i > $i).
% 0.23/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.52  thf(k8_eqrel_1_type, type, k8_eqrel_1: $i > $i > $i).
% 0.23/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.52  thf(m2_subset_1_type, type, m2_subset_1: $i > $i > $i > $o).
% 0.23/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.23/0.52  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.23/0.52  thf(m2_filter_1_type, type, m2_filter_1: $i > $i > $i > $o).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(t8_filter_1, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.23/0.52             ( v8_relat_2 @ B ) & 
% 0.23/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.23/0.52               ( ![D:$i]:
% 0.23/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.23/0.52                   ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.23/0.52                     ( r3_binop_1 @
% 0.23/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.23/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.23/0.52                ( v8_relat_2 @ B ) & 
% 0.23/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52              ( ![C:$i]:
% 0.23/0.52                ( ( m1_subset_1 @ C @ A ) =>
% 0.23/0.52                  ( ![D:$i]:
% 0.23/0.52                    ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.23/0.52                      ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.23/0.52                        ( r3_binop_1 @
% 0.23/0.52                          ( k8_eqrel_1 @ A @ B ) @ 
% 0.23/0.52                          ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.23/0.52                          ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t8_filter_1])).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      (~ (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(redefinition_k8_eqrel_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52       ( ( k8_eqrel_1 @ A @ B ) = ( k7_eqrel_1 @ A @ B ) ) ))).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X28 : $i, X29 : $i]:
% 0.23/0.52         (((k8_eqrel_1 @ X28 @ X29) = (k7_eqrel_1 @ X28 @ X29))
% 0.23/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.23/0.52          | ~ (v1_partfun1 @ X29 @ X28)
% 0.23/0.52          | ~ (v8_relat_2 @ X29)
% 0.23/0.52          | ~ (v3_relat_2 @ X29))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k8_eqrel_1])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      ((~ (v3_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.23/0.52        | ((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.52  thf('4', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('5', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('6', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('7', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (~ (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.23/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.23/0.52  thf('9', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('10', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(dt_m2_filter_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) ) =>
% 0.23/0.52       ( ![C:$i]:
% 0.23/0.52         ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.23/0.52           ( ( v1_funct_1 @ C ) & 
% 0.23/0.52             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.23/0.52             ( m1_subset_1 @
% 0.23/0.52               C @ 
% 0.23/0.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) ))).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X23)
% 0.23/0.52          | ~ (v1_relat_1 @ X24)
% 0.23/0.52          | (m1_subset_1 @ X25 @ 
% 0.23/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23) @ X23)))
% 0.23/0.52          | ~ (m2_filter_1 @ X25 @ X23 @ X24))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (((m1_subset_1 @ sk_D @ 
% 0.23/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.23/0.52        | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(cc2_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X2 : $i, X3 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.23/0.52          | (v1_relat_1 @ X2)
% 0.23/0.52          | ~ (v1_relat_1 @ X3))),
% 0.23/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf(fc6_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.23/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.52  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (((m1_subset_1 @ sk_D @ 
% 0.23/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.23/0.52        | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['12', '17'])).
% 0.23/0.52  thf('19', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_D @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf(d7_binop_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ B @ A ) =>
% 0.23/0.52       ( ![C:$i]:
% 0.23/0.52         ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.52             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.23/0.52             ( m1_subset_1 @
% 0.23/0.52               C @ 
% 0.23/0.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.23/0.52           ( ( r3_binop_1 @ A @ B @ C ) <=>
% 0.23/0.52             ( ( r1_binop_1 @ A @ B @ C ) & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.52         (~ (v1_funct_1 @ X10)
% 0.23/0.52          | ~ (v1_funct_2 @ X10 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 0.23/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 0.23/0.52          | ~ (r3_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | (r2_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | ~ (m1_subset_1 @ X12 @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.23/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.52  thf('23', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X23)
% 0.23/0.52          | ~ (v1_relat_1 @ X24)
% 0.23/0.52          | (v1_funct_2 @ X25 @ (k2_zfmisc_1 @ X23 @ X23) @ X23)
% 0.23/0.52          | ~ (m2_filter_1 @ X25 @ X23 @ X24))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.23/0.52        | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52        | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.23/0.52  thf('28', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('29', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.23/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf('30', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X23)
% 0.23/0.52          | ~ (v1_relat_1 @ X24)
% 0.23/0.52          | (v1_funct_1 @ X25)
% 0.23/0.52          | ~ (m2_filter_1 @ X25 @ X23 @ X24))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (((v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.52  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf('34', plain, (((v1_funct_1 @ sk_D) | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.52  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('37', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.23/0.52      inference('demod', [status(thm)], ['22', '29', '36'])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      (((r2_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['9', '37'])).
% 0.23/0.52  thf('39', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('40', plain, ((r2_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.23/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.52  thf('41', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('42', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t7_filter_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.23/0.52             ( v8_relat_2 @ B ) & 
% 0.23/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.23/0.52               ( ![D:$i]:
% 0.23/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.23/0.52                   ( ( r2_binop_1 @ A @ C @ D ) =>
% 0.23/0.52                     ( r2_binop_1 @
% 0.23/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.23/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('43', plain,
% 0.23/0.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.23/0.52         (~ (v1_partfun1 @ X34 @ X35)
% 0.23/0.52          | ~ (v3_relat_2 @ X34)
% 0.23/0.52          | ~ (v8_relat_2 @ X34)
% 0.23/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.23/0.52          | ~ (m2_filter_1 @ X36 @ X35 @ X34)
% 0.23/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ X35 @ X34) @ 
% 0.23/0.52             (k9_eqrel_1 @ X35 @ X34 @ X37) @ (k3_filter_1 @ X35 @ X34 @ X36))
% 0.23/0.52          | ~ (r2_binop_1 @ X35 @ X37 @ X36)
% 0.23/0.52          | ~ (m1_subset_1 @ X37 @ X35)
% 0.23/0.52          | (v1_xboole_0 @ X35))),
% 0.23/0.52      inference('cnf', [status(esa)], [t7_filter_1])).
% 0.23/0.52  thf('44', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.23/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.23/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.23/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.23/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.52  thf('45', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('46', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('47', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('48', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('49', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.23/0.52          | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.23/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.23/0.52  thf('50', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['41', '49'])).
% 0.23/0.52  thf('51', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.23/0.52        | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['40', '50'])).
% 0.23/0.52  thf('52', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('53', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.23/0.52  thf('54', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('55', plain,
% 0.23/0.52      ((r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.23/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.23/0.52  thf('56', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('57', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_D @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf(dt_k3_filter_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_partfun1 @ B @ A ) & 
% 0.23/0.52         ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.23/0.52         ( v1_funct_1 @ C ) & 
% 0.23/0.52         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.23/0.52         ( m1_subset_1 @
% 0.23/0.52           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.23/0.52       ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) ) & 
% 0.23/0.52         ( v1_funct_2 @
% 0.23/0.52           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.23/0.52           ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.23/0.52           ( k8_eqrel_1 @ A @ B ) ) & 
% 0.23/0.52         ( m1_subset_1 @
% 0.23/0.52           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.23/0.52           ( k1_zfmisc_1 @
% 0.23/0.52             ( k2_zfmisc_1 @
% 0.23/0.52               ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.23/0.52               ( k8_eqrel_1 @ A @ B ) ) ) ) ) ))).
% 0.23/0.52  thf('58', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.23/0.52          | ~ (v8_relat_2 @ X13)
% 0.23/0.52          | ~ (v3_relat_2 @ X13)
% 0.23/0.52          | ~ (v1_partfun1 @ X13 @ X14)
% 0.23/0.52          | (v1_xboole_0 @ X14)
% 0.23/0.52          | ~ (v1_funct_1 @ X15)
% 0.23/0.52          | ~ (v1_funct_2 @ X15 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 0.23/0.52          | (m1_subset_1 @ (k3_filter_1 @ X14 @ X13 @ X15) @ 
% 0.23/0.52             (k1_zfmisc_1 @ 
% 0.23/0.52              (k2_zfmisc_1 @ 
% 0.23/0.52               (k2_zfmisc_1 @ (k8_eqrel_1 @ X14 @ X13) @ 
% 0.23/0.52                (k8_eqrel_1 @ X14 @ X13)) @ 
% 0.23/0.52               (k8_eqrel_1 @ X14 @ X13)))))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.23/0.52  thf('59', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.52           (k1_zfmisc_1 @ 
% 0.23/0.52            (k2_zfmisc_1 @ 
% 0.23/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.23/0.52             (k8_eqrel_1 @ sk_A @ X0))))
% 0.23/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ X0)
% 0.23/0.52          | ~ (v8_relat_2 @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf('60', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.23/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('62', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.52           (k1_zfmisc_1 @ 
% 0.23/0.52            (k2_zfmisc_1 @ 
% 0.23/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.23/0.52             (k8_eqrel_1 @ sk_A @ X0))))
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ X0)
% 0.23/0.52          | ~ (v8_relat_2 @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.23/0.52  thf('63', plain,
% 0.23/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.23/0.52        | (v1_xboole_0 @ sk_A)
% 0.23/0.52        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52           (k1_zfmisc_1 @ 
% 0.23/0.52            (k2_zfmisc_1 @ 
% 0.23/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['56', '62'])).
% 0.23/0.52  thf('64', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('65', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('66', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('67', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('68', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('69', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('70', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52           (k1_zfmisc_1 @ 
% 0.23/0.52            (k2_zfmisc_1 @ 
% 0.23/0.52             (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52              (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52             (k7_eqrel_1 @ sk_A @ sk_B)))))),
% 0.23/0.52      inference('demod', [status(thm)],
% 0.23/0.52                ['63', '64', '65', '66', '67', '68', '69'])).
% 0.23/0.52  thf('71', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('72', plain,
% 0.23/0.52      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52        (k1_zfmisc_1 @ 
% 0.23/0.52         (k2_zfmisc_1 @ 
% 0.23/0.52          (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52          (k7_eqrel_1 @ sk_A @ sk_B))))),
% 0.23/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.23/0.52  thf('73', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.52         (~ (v1_funct_1 @ X10)
% 0.23/0.52          | ~ (v1_funct_2 @ X10 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 0.23/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 0.23/0.52          | ~ (r1_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | ~ (r2_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | (r3_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | ~ (m1_subset_1 @ X12 @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.23/0.52  thf('74', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52               (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52                (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52               (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.23/0.52  thf('75', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('76', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_D @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf('77', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.23/0.52          | ~ (v8_relat_2 @ X13)
% 0.23/0.52          | ~ (v3_relat_2 @ X13)
% 0.23/0.52          | ~ (v1_partfun1 @ X13 @ X14)
% 0.23/0.52          | (v1_xboole_0 @ X14)
% 0.23/0.52          | ~ (v1_funct_1 @ X15)
% 0.23/0.52          | ~ (v1_funct_2 @ X15 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 0.23/0.52          | (v1_funct_1 @ (k3_filter_1 @ X14 @ X13 @ X15)))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.23/0.52  thf('78', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.23/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ X0)
% 0.23/0.52          | ~ (v8_relat_2 @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.23/0.52  thf('79', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.23/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('81', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ X0)
% 0.23/0.52          | ~ (v8_relat_2 @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.23/0.52  thf('82', plain,
% 0.23/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.23/0.52        | (v1_xboole_0 @ sk_A)
% 0.23/0.52        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['75', '81'])).
% 0.23/0.52  thf('83', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('84', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('85', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('86', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.23/0.52  thf('87', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('88', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.23/0.52      inference('clc', [status(thm)], ['86', '87'])).
% 0.23/0.52  thf('89', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52               (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52                (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52               (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('demod', [status(thm)], ['74', '88'])).
% 0.23/0.52  thf('90', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('91', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_D @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf('92', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.23/0.52          | ~ (v8_relat_2 @ X13)
% 0.23/0.52          | ~ (v3_relat_2 @ X13)
% 0.23/0.52          | ~ (v1_partfun1 @ X13 @ X14)
% 0.23/0.52          | (v1_xboole_0 @ X14)
% 0.23/0.52          | ~ (v1_funct_1 @ X15)
% 0.23/0.52          | ~ (v1_funct_2 @ X15 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 0.23/0.52          | (v1_funct_2 @ (k3_filter_1 @ X14 @ X13 @ X15) @ 
% 0.23/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ X14 @ X13) @ (k8_eqrel_1 @ X14 @ X13)) @ 
% 0.23/0.52             (k8_eqrel_1 @ X14 @ X13)))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.23/0.52  thf('93', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.23/0.52           (k8_eqrel_1 @ sk_A @ X0))
% 0.23/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ X0)
% 0.23/0.52          | ~ (v8_relat_2 @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['91', '92'])).
% 0.23/0.52  thf('94', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.23/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('96', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.23/0.52           (k8_eqrel_1 @ sk_A @ X0))
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ X0)
% 0.23/0.52          | ~ (v8_relat_2 @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.23/0.52  thf('97', plain,
% 0.23/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.23/0.52        | (v1_xboole_0 @ sk_A)
% 0.23/0.52        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['90', '96'])).
% 0.23/0.52  thf('98', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('99', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('100', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('101', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('102', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('103', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('104', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52           (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52            (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52           (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('demod', [status(thm)],
% 0.23/0.52                ['97', '98', '99', '100', '101', '102', '103'])).
% 0.23/0.52  thf('105', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('106', plain,
% 0.23/0.52      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.52        (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.23/0.52        (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('clc', [status(thm)], ['104', '105'])).
% 0.23/0.52  thf('107', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.23/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('demod', [status(thm)], ['89', '106'])).
% 0.23/0.52  thf('108', plain,
% 0.23/0.52      ((~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52        | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52        | ~ (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52             (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['55', '107'])).
% 0.23/0.52  thf('109', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('110', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_D @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf('111', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.52         (~ (v1_funct_1 @ X10)
% 0.23/0.52          | ~ (v1_funct_2 @ X10 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 0.23/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 0.23/0.52          | ~ (r3_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | (r1_binop_1 @ X11 @ X12 @ X10)
% 0.23/0.52          | ~ (m1_subset_1 @ X12 @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.23/0.52  thf('112', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.23/0.52      inference('sup-', [status(thm)], ['110', '111'])).
% 0.23/0.52  thf('113', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.23/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf('114', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('115', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.23/0.52      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.23/0.52  thf('116', plain,
% 0.23/0.52      (((r1_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['109', '115'])).
% 0.23/0.52  thf('117', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('118', plain, ((r1_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.23/0.52      inference('demod', [status(thm)], ['116', '117'])).
% 0.23/0.52  thf('119', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('120', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t6_filter_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.23/0.52             ( v8_relat_2 @ B ) & 
% 0.23/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.23/0.52               ( ![D:$i]:
% 0.23/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.23/0.52                   ( ( r1_binop_1 @ A @ C @ D ) =>
% 0.23/0.52                     ( r1_binop_1 @
% 0.23/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.23/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('121', plain,
% 0.23/0.52      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.23/0.52         (~ (v1_partfun1 @ X30 @ X31)
% 0.23/0.52          | ~ (v3_relat_2 @ X30)
% 0.23/0.52          | ~ (v8_relat_2 @ X30)
% 0.23/0.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.23/0.52          | ~ (m2_filter_1 @ X32 @ X31 @ X30)
% 0.23/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ X31 @ X30) @ 
% 0.23/0.52             (k9_eqrel_1 @ X31 @ X30 @ X33) @ (k3_filter_1 @ X31 @ X30 @ X32))
% 0.23/0.52          | ~ (r1_binop_1 @ X31 @ X33 @ X32)
% 0.23/0.52          | ~ (m1_subset_1 @ X33 @ X31)
% 0.23/0.52          | (v1_xboole_0 @ X31))),
% 0.23/0.52      inference('cnf', [status(esa)], [t6_filter_1])).
% 0.23/0.52  thf('122', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.23/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.23/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.23/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.23/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['120', '121'])).
% 0.23/0.52  thf('123', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('124', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('125', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('126', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('127', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.23/0.52          | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.23/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.23/0.52  thf('128', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.23/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['119', '127'])).
% 0.23/0.52  thf('129', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.23/0.52        | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['118', '128'])).
% 0.23/0.52  thf('130', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('131', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A)
% 0.23/0.52        | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.23/0.52      inference('demod', [status(thm)], ['129', '130'])).
% 0.23/0.52  thf('132', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('133', plain,
% 0.23/0.52      ((r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.23/0.52      inference('clc', [status(thm)], ['131', '132'])).
% 0.23/0.52  thf('134', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('135', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(dt_k9_eqrel_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.23/0.52         ( v1_partfun1 @ B @ A ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.23/0.52         ( m1_subset_1 @ C @ A ) ) =>
% 0.23/0.52       ( m2_subset_1 @
% 0.23/0.52         ( k9_eqrel_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) @ 
% 0.23/0.52         ( k8_eqrel_1 @ A @ B ) ) ))).
% 0.23/0.52  thf('136', plain,
% 0.23/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.23/0.52          | ~ (v1_partfun1 @ X18 @ X19)
% 0.23/0.52          | ~ (v8_relat_2 @ X18)
% 0.23/0.52          | ~ (v3_relat_2 @ X18)
% 0.23/0.52          | (v1_xboole_0 @ X19)
% 0.23/0.52          | ~ (m1_subset_1 @ X20 @ X19)
% 0.23/0.52          | (m2_subset_1 @ (k9_eqrel_1 @ X19 @ X18 @ X20) @ 
% 0.23/0.52             (k1_zfmisc_1 @ X19) @ (k8_eqrel_1 @ X19 @ X18)))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k9_eqrel_1])).
% 0.23/0.52  thf('137', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.23/0.52           (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (v1_xboole_0 @ sk_A)
% 0.23/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.23/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['135', '136'])).
% 0.23/0.52  thf('138', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('139', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('140', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('141', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('142', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.23/0.52           (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.23/0.52  thf('143', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('144', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.52          | (m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.23/0.52             (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['142', '143'])).
% 0.23/0.52  thf('145', plain,
% 0.23/0.52      ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52        (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['134', '144'])).
% 0.23/0.52  thf('146', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(dt_k8_eqrel_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52       ( m1_eqrel_1 @ ( k8_eqrel_1 @ A @ B ) @ A ) ))).
% 0.23/0.52  thf('147', plain,
% 0.23/0.52      (![X16 : $i, X17 : $i]:
% 0.23/0.52         ((m1_eqrel_1 @ (k8_eqrel_1 @ X16 @ X17) @ X16)
% 0.23/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.23/0.52          | ~ (v1_partfun1 @ X17 @ X16)
% 0.23/0.52          | ~ (v8_relat_2 @ X17)
% 0.23/0.52          | ~ (v3_relat_2 @ X17))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k8_eqrel_1])).
% 0.23/0.52  thf('148', plain,
% 0.23/0.52      ((~ (v3_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.23/0.52        | (m1_eqrel_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['146', '147'])).
% 0.23/0.52  thf('149', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('150', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('151', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('152', plain, ((m1_eqrel_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.52      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 0.23/0.52  thf(dt_m1_eqrel_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_eqrel_1 @ B @ A ) =>
% 0.23/0.52       ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.23/0.52  thf('153', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i]:
% 0.23/0.52         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22)))
% 0.23/0.52          | ~ (m1_eqrel_1 @ X21 @ X22))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_m1_eqrel_1])).
% 0.23/0.52  thf('154', plain,
% 0.23/0.52      ((m1_subset_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['152', '153'])).
% 0.23/0.52  thf('155', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('156', plain,
% 0.23/0.52      ((m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['154', '155'])).
% 0.23/0.52  thf(redefinition_m2_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.52       ( ![C:$i]: ( ( m2_subset_1 @ C @ A @ B ) <=> ( m1_subset_1 @ C @ B ) ) ) ))).
% 0.23/0.52  thf('157', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X6)
% 0.23/0.52          | (v1_xboole_0 @ X7)
% 0.23/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.23/0.52          | (m1_subset_1 @ X9 @ X7)
% 0.23/0.52          | ~ (m2_subset_1 @ X9 @ X6 @ X7))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.23/0.52  thf('158', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m2_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.23/0.52             (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['156', '157'])).
% 0.23/0.52  thf('159', plain,
% 0.23/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.52        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52        | (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52           (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['145', '158'])).
% 0.23/0.52  thf('160', plain,
% 0.23/0.52      ((m1_subset_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['152', '153'])).
% 0.23/0.52  thf(cc1_subset_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.23/0.52  thf('161', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.23/0.52          | (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.23/0.52  thf('162', plain,
% 0.23/0.52      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.52        | (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['160', '161'])).
% 0.23/0.52  thf('163', plain,
% 0.23/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.23/0.52  thf('164', plain,
% 0.23/0.52      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.52        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('demod', [status(thm)], ['162', '163'])).
% 0.23/0.52  thf('165', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(fc3_eqrel_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.23/0.52         ( v1_partfun1 @ B @ A ) & 
% 0.23/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.52       ( ~( v1_xboole_0 @ ( k7_eqrel_1 @ A @ B ) ) ) ))).
% 0.23/0.52  thf('166', plain,
% 0.23/0.52      (![X26 : $i, X27 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X26)
% 0.23/0.52          | ~ (v3_relat_2 @ X27)
% 0.23/0.52          | ~ (v8_relat_2 @ X27)
% 0.23/0.52          | ~ (v1_partfun1 @ X27 @ X26)
% 0.23/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.23/0.52          | ~ (v1_xboole_0 @ (k7_eqrel_1 @ X26 @ X27)))),
% 0.23/0.52      inference('cnf', [status(esa)], [fc3_eqrel_1])).
% 0.23/0.52  thf('167', plain,
% 0.23/0.52      ((~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.23/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.23/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.23/0.52        | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['165', '166'])).
% 0.23/0.52  thf('168', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('169', plain, ((v8_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('170', plain, ((v3_relat_2 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('171', plain,
% 0.23/0.52      ((~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 0.23/0.52  thf('172', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('173', plain, (~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('clc', [status(thm)], ['171', '172'])).
% 0.23/0.52  thf('174', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.52      inference('clc', [status(thm)], ['164', '173'])).
% 0.23/0.52  thf('175', plain,
% 0.23/0.52      (((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52         (k7_eqrel_1 @ sk_A @ sk_B))
% 0.23/0.52        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['159', '174'])).
% 0.23/0.52  thf('176', plain, (~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('clc', [status(thm)], ['171', '172'])).
% 0.23/0.52  thf('177', plain,
% 0.23/0.52      ((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.52        (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('clc', [status(thm)], ['175', '176'])).
% 0.23/0.52  thf('178', plain,
% 0.23/0.52      ((r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.23/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.23/0.52      inference('demod', [status(thm)], ['108', '133', '177'])).
% 0.23/0.52  thf('179', plain, ($false), inference('demod', [status(thm)], ['8', '178'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
