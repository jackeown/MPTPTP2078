%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bkr954kMrZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 748 expanded)
%              Number of leaves         :   37 ( 236 expanded)
%              Depth                    :   16
%              Number of atoms          : 2250 (15278 expanded)
%              Number of equality atoms :   13 (  40 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

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

thf(k7_eqrel_1_type,type,(
    k7_eqrel_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

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
    ! [X26: $i,X27: $i] :
      ( ( ( k8_eqrel_1 @ X26 @ X27 )
        = ( k7_eqrel_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v1_partfun1 @ X27 @ X26 )
      | ~ ( v8_relat_2 @ X27 )
      | ~ ( v3_relat_2 @ X27 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) @ X21 ) ) )
      | ~ ( m2_filter_1 @ X23 @ X21 @ X22 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_funct_2 @ X23 @ ( k2_zfmisc_1 @ X21 @ X21 ) @ X21 )
      | ~ ( m2_filter_1 @ X23 @ X21 @ X22 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_funct_1 @ X23 )
      | ~ ( m2_filter_1 @ X23 @ X21 @ X22 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v3_relat_2 @ X32 )
      | ~ ( v8_relat_2 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( m2_filter_1 @ X34 @ X33 @ X32 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ X33 @ X32 ) @ ( k9_eqrel_1 @ X33 @ X32 @ X35 ) @ ( k3_filter_1 @ X33 @ X32 @ X34 ) )
      | ~ ( r2_binop_1 @ X33 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
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
      | ( v1_funct_2 @ ( k3_filter_1 @ X14 @ X13 @ X15 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X14 @ X13 ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
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
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
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
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
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
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('87',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('88',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('97',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['74','91','105'])).

thf('107',plain,
    ( ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','106'])).

thf('108',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) @ X11 ) ) )
      | ~ ( r3_binop_1 @ X11 @ X12 @ X10 )
      | ( r1_binop_1 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['34','35'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r1_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
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

thf('120',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v3_relat_2 @ X28 )
      | ~ ( v8_relat_2 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( m2_filter_1 @ X30 @ X29 @ X28 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ X29 @ X28 ) @ ( k9_eqrel_1 @ X29 @ X28 @ X31 ) @ ( k3_filter_1 @ X29 @ X28 @ X30 ) )
      | ~ ( r1_binop_1 @ X29 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('123',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
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

thf('135',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v8_relat_2 @ X18 )
      | ~ ( v3_relat_2 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X19 @ X18 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) @ ( k8_eqrel_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('138',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['133','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( m1_subset_1 @ ( k7_eqrel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('146',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k7_eqrel_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v8_relat_2 @ X17 )
      | ~ ( v3_relat_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_eqrel_1])).

thf('147',plain,
    ( ~ ( v3_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('152',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X9 @ X7 )
      | ~ ( m2_subset_1 @ X9 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('157',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
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

thf('159',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v3_relat_2 @ X25 )
      | ~ ( v8_relat_2 @ X25 )
      | ~ ( v1_partfun1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_eqrel_1])).

thf('160',plain,
    ( ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['157','166'])).

thf('168',plain,
    ( ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['154','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('170',plain,(
    m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['107','132','170'])).

thf('172',plain,(
    $false ),
    inference(demod,[status(thm)],['8','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bkr954kMrZ
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 74 iterations in 0.051s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_binop_1_type, type, r1_binop_1: $i > $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.20/0.51  thf(r3_binop_1_type, type, r3_binop_1: $i > $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k7_eqrel_1_type, type, k7_eqrel_1: $i > $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(r2_binop_1_type, type, r2_binop_1: $i > $i > $i > $o).
% 0.20/0.51  thf(k9_eqrel_1_type, type, k9_eqrel_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(m2_filter_1_type, type, m2_filter_1: $i > $i > $i > $o).
% 0.20/0.51  thf(k3_filter_1_type, type, k3_filter_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k8_eqrel_1_type, type, k8_eqrel_1: $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(m2_subset_1_type, type, m2_subset_1: $i > $i > $i > $o).
% 0.20/0.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.20/0.51  thf(t8_filter_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.20/0.51             ( v8_relat_2 @ B ) & 
% 0.20/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.20/0.51                   ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.20/0.51                     ( r3_binop_1 @
% 0.20/0.51                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.20/0.51                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.20/0.51                ( v8_relat_2 @ B ) & 
% 0.20/0.51                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.20/0.51                      ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.20/0.51                        ( r3_binop_1 @
% 0.20/0.51                          ( k8_eqrel_1 @ A @ B ) @ 
% 0.20/0.51                          ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.20/0.51                          ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t8_filter_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (~ (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k8_eqrel_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51       ( ( k8_eqrel_1 @ A @ B ) = ( k7_eqrel_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i]:
% 0.20/0.51         (((k8_eqrel_1 @ X26 @ X27) = (k7_eqrel_1 @ X26 @ X27))
% 0.20/0.51          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.20/0.51          | ~ (v1_partfun1 @ X27 @ X26)
% 0.20/0.51          | ~ (v8_relat_2 @ X27)
% 0.20/0.51          | ~ (v3_relat_2 @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k8_eqrel_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((~ (v3_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v8_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.51        | ((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (~ (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.51  thf('9', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m2_filter_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.20/0.51           ( ( v1_funct_1 @ C ) & 
% 0.20/0.51             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.20/0.51             ( m1_subset_1 @
% 0.20/0.51               C @ 
% 0.20/0.51               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X22)
% 0.20/0.51          | (m1_subset_1 @ X23 @ 
% 0.20/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21) @ X21)))
% 0.20/0.51          | ~ (m2_filter_1 @ X23 @ X21 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_D @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.51          | (v1_relat_1 @ X2)
% 0.20/0.51          | ~ (v1_relat_1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_D @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.20/0.51        | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '17'])).
% 0.20/0.51  thf('19', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf(d7_binop_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.20/0.51             ( m1_subset_1 @
% 0.20/0.51               C @ 
% 0.20/0.51               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.20/0.51           ( ( r3_binop_1 @ A @ B @ C ) <=>
% 0.20/0.51             ( ( r1_binop_1 @ A @ B @ C ) & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_funct_2 @ X10 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 0.20/0.51          | ~ (r3_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | (r2_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X22)
% 0.20/0.51          | (v1_funct_2 @ X23 @ (k2_zfmisc_1 @ X21 @ X21) @ X21)
% 0.20/0.51          | ~ (m2_filter_1 @ X23 @ X21 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X22)
% 0.20/0.51          | (v1_funct_1 @ X23)
% 0.20/0.51          | ~ (m2_filter_1 @ X23 @ X21 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('34', plain, (((v1_funct_1 @ sk_D) | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '29', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((r2_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '37'])).
% 0.20/0.51  thf('39', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain, ((r2_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t7_filter_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.20/0.51             ( v8_relat_2 @ B ) & 
% 0.20/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.20/0.51                   ( ( r2_binop_1 @ A @ C @ D ) =>
% 0.20/0.51                     ( r2_binop_1 @
% 0.20/0.51                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.20/0.51                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.51         (~ (v1_partfun1 @ X32 @ X33)
% 0.20/0.51          | ~ (v3_relat_2 @ X32)
% 0.20/0.51          | ~ (v8_relat_2 @ X32)
% 0.20/0.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.20/0.51          | ~ (m2_filter_1 @ X34 @ X33 @ X32)
% 0.20/0.51          | (r2_binop_1 @ (k8_eqrel_1 @ X33 @ X32) @ 
% 0.20/0.51             (k9_eqrel_1 @ X33 @ X32 @ X35) @ (k3_filter_1 @ X33 @ X32 @ X34))
% 0.20/0.51          | ~ (r2_binop_1 @ X33 @ X35 @ X34)
% 0.20/0.51          | ~ (m1_subset_1 @ X35 @ X33)
% 0.20/0.51          | (v1_xboole_0 @ X33))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_filter_1])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.20/0.51          | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.20/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.20/0.51          | ~ (v8_relat_2 @ sk_B)
% 0.20/0.51          | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('46', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('48', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.20/0.51          | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.20/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.20/0.51        | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '50'])).
% 0.20/0.51  thf('52', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf(dt_k3_filter_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_partfun1 @ B @ A ) & 
% 0.20/0.51         ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.20/0.51         ( v1_funct_1 @ C ) & 
% 0.20/0.51         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.20/0.51         ( m1_subset_1 @
% 0.20/0.51           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.20/0.51       ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) ) & 
% 0.20/0.51         ( v1_funct_2 @
% 0.20/0.51           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.20/0.51           ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.20/0.51           ( k8_eqrel_1 @ A @ B ) ) & 
% 0.20/0.51         ( m1_subset_1 @
% 0.20/0.51           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.20/0.51           ( k1_zfmisc_1 @
% 0.20/0.51             ( k2_zfmisc_1 @
% 0.20/0.51               ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.20/0.51               ( k8_eqrel_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.20/0.51          | ~ (v8_relat_2 @ X13)
% 0.20/0.51          | ~ (v3_relat_2 @ X13)
% 0.20/0.51          | ~ (v1_partfun1 @ X13 @ X14)
% 0.20/0.51          | (v1_xboole_0 @ X14)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 0.20/0.51          | (m1_subset_1 @ (k3_filter_1 @ X14 @ X13 @ X15) @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k8_eqrel_1 @ X14 @ X13) @ 
% 0.20/0.51                (k8_eqrel_1 @ X14 @ X13)) @ 
% 0.20/0.51               (k8_eqrel_1 @ X14 @ X13)))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (k2_zfmisc_1 @ 
% 0.20/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.20/0.51             (k8_eqrel_1 @ sk_A @ X0))))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ X0)
% 0.20/0.51          | ~ (v8_relat_2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (k2_zfmisc_1 @ 
% 0.20/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.20/0.51             (k8_eqrel_1 @ sk_A @ X0))))
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ X0)
% 0.20/0.51          | ~ (v8_relat_2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (k2_zfmisc_1 @ 
% 0.20/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['56', '62'])).
% 0.20/0.51  thf('64', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('68', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('69', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (k2_zfmisc_1 @ 
% 0.20/0.51             (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51              (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51             (k7_eqrel_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['63', '64', '65', '66', '67', '68', '69'])).
% 0.20/0.51  thf('71', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ 
% 0.20/0.51          (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51          (k7_eqrel_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_funct_2 @ X10 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 0.20/0.51          | ~ (r1_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | ~ (r2_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | (r3_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.20/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.20/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.20/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51                (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51               (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.20/0.51          | ~ (v8_relat_2 @ X13)
% 0.20/0.51          | ~ (v3_relat_2 @ X13)
% 0.20/0.51          | ~ (v1_partfun1 @ X13 @ X14)
% 0.20/0.51          | (v1_xboole_0 @ X14)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 0.20/0.51          | (v1_funct_2 @ (k3_filter_1 @ X14 @ X13 @ X15) @ 
% 0.20/0.51             (k2_zfmisc_1 @ (k8_eqrel_1 @ X14 @ X13) @ (k8_eqrel_1 @ X14 @ X13)) @ 
% 0.20/0.51             (k8_eqrel_1 @ X14 @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.20/0.51           (k8_eqrel_1 @ sk_A @ X0))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ X0)
% 0.20/0.51          | ~ (v8_relat_2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.51  thf('79', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.20/0.51           (k8_eqrel_1 @ sk_A @ X0))
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ X0)
% 0.20/0.51          | ~ (v8_relat_2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ sk_A)
% 0.20/0.51        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['75', '81'])).
% 0.20/0.51  thf('83', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('86', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('87', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('88', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51           (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51            (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51           (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.20/0.51  thf('90', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.51        (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51        (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.20/0.51          | ~ (v8_relat_2 @ X13)
% 0.20/0.51          | ~ (v3_relat_2 @ X13)
% 0.20/0.51          | ~ (v1_partfun1 @ X13 @ X14)
% 0.20/0.51          | (v1_xboole_0 @ X14)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14) @ X14)))
% 0.20/0.51          | (v1_funct_1 @ (k3_filter_1 @ X14 @ X13 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ X0)
% 0.20/0.51          | ~ (v8_relat_2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ X0)
% 0.20/0.51          | ~ (v8_relat_2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      ((~ (v8_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ sk_A)
% 0.20/0.51        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['92', '98'])).
% 0.20/0.51  thf('100', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.20/0.51  thf('104', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('105', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.20/0.51             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.20/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.20/0.51               (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['74', '91', '105'])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      ((~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51        | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51        | ~ (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51             (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '106'])).
% 0.20/0.51  thf('108', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_funct_2 @ X10 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X11) @ X11)))
% 0.20/0.51          | ~ (r3_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | (r1_binop_1 @ X11 @ X12 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.51  thf('112', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      (((r1_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['108', '114'])).
% 0.20/0.51  thf('116', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('117', plain, ((r1_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['115', '116'])).
% 0.20/0.51  thf('118', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('119', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t6_filter_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.20/0.51             ( v8_relat_2 @ B ) & 
% 0.20/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.20/0.51                   ( ( r1_binop_1 @ A @ C @ D ) =>
% 0.20/0.51                     ( r1_binop_1 @
% 0.20/0.51                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.20/0.51                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.51         (~ (v1_partfun1 @ X28 @ X29)
% 0.20/0.51          | ~ (v3_relat_2 @ X28)
% 0.20/0.51          | ~ (v8_relat_2 @ X28)
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.20/0.51          | ~ (m2_filter_1 @ X30 @ X29 @ X28)
% 0.20/0.51          | (r1_binop_1 @ (k8_eqrel_1 @ X29 @ X28) @ 
% 0.20/0.51             (k9_eqrel_1 @ X29 @ X28 @ X31) @ (k3_filter_1 @ X29 @ X28 @ X30))
% 0.20/0.51          | ~ (r1_binop_1 @ X29 @ X31 @ X30)
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ X29)
% 0.20/0.51          | (v1_xboole_0 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_filter_1])).
% 0.20/0.51  thf('121', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.20/0.51          | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.20/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.20/0.51          | ~ (v8_relat_2 @ sk_B)
% 0.20/0.51          | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.51  thf('122', plain,
% 0.20/0.51      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('123', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('124', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('125', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('126', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.20/0.51          | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.20/0.51          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 0.20/0.51  thf('127', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.51          | ~ (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['118', '126'])).
% 0.20/0.51  thf('128', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.20/0.51        | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['117', '127'])).
% 0.20/0.51  thf('129', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('130', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_A)
% 0.20/0.51        | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['128', '129'])).
% 0.20/0.51  thf('131', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('132', plain,
% 0.20/0.51      ((r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['130', '131'])).
% 0.20/0.51  thf('133', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('134', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k9_eqrel_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.20/0.51         ( v1_partfun1 @ B @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ A ) ) =>
% 0.20/0.51       ( m2_subset_1 @
% 0.20/0.51         ( k9_eqrel_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) @ 
% 0.20/0.51         ( k8_eqrel_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('135', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.20/0.51          | ~ (v1_partfun1 @ X18 @ X19)
% 0.20/0.51          | ~ (v8_relat_2 @ X18)
% 0.20/0.51          | ~ (v3_relat_2 @ X18)
% 0.20/0.51          | (v1_xboole_0 @ X19)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ X19)
% 0.20/0.51          | (m2_subset_1 @ (k9_eqrel_1 @ X19 @ X18 @ X20) @ 
% 0.20/0.51             (k1_zfmisc_1 @ X19) @ (k8_eqrel_1 @ X19 @ X18)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k9_eqrel_1])).
% 0.20/0.51  thf('136', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.20/0.51           (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (v1_xboole_0 @ sk_A)
% 0.20/0.51          | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51          | ~ (v8_relat_2 @ sk_B)
% 0.20/0.51          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['134', '135'])).
% 0.20/0.51  thf('137', plain,
% 0.20/0.51      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.51  thf('138', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('139', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('140', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('141', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.20/0.51           (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 0.20/0.51  thf('142', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('143', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | (m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['141', '142'])).
% 0.20/0.51  thf('144', plain,
% 0.20/0.51      ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['133', '143'])).
% 0.20/0.51  thf('145', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k7_eqrel_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( k7_eqrel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.51  thf('146', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k7_eqrel_1 @ X16 @ X17) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.20/0.51          | ~ (v1_partfun1 @ X17 @ X16)
% 0.20/0.51          | ~ (v8_relat_2 @ X17)
% 0.20/0.51          | ~ (v3_relat_2 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k7_eqrel_1])).
% 0.20/0.51  thf('147', plain,
% 0.20/0.51      ((~ (v3_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v8_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['145', '146'])).
% 0.20/0.51  thf('148', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('149', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('150', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('151', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.20/0.51  thf(redefinition_m2_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ![C:$i]: ( ( m2_subset_1 @ C @ A @ B ) <=> ( m1_subset_1 @ C @ B ) ) ) ))).
% 0.20/0.51  thf('152', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X6)
% 0.20/0.51          | (v1_xboole_0 @ X7)
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.20/0.51          | (m1_subset_1 @ X9 @ X7)
% 0.20/0.51          | ~ (m2_subset_1 @ X9 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.20/0.51  thf('153', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m2_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.51             (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.51  thf('154', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51        | (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51           (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['144', '153'])).
% 0.20/0.51  thf('155', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.20/0.51  thf(cc1_subset_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.51  thf('156', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.51          | (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.51  thf('157', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['155', '156'])).
% 0.20/0.51  thf('158', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(fc3_eqrel_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.20/0.51         ( v1_partfun1 @ B @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( k7_eqrel_1 @ A @ B ) ) ) ))).
% 0.20/0.51  thf('159', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X24)
% 0.20/0.51          | ~ (v3_relat_2 @ X25)
% 0.20/0.51          | ~ (v8_relat_2 @ X25)
% 0.20/0.51          | ~ (v1_partfun1 @ X25 @ X24)
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.20/0.51          | ~ (v1_xboole_0 @ (k7_eqrel_1 @ X24 @ X25)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc3_eqrel_1])).
% 0.20/0.51  thf('160', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v8_relat_2 @ sk_B)
% 0.20/0.51        | ~ (v3_relat_2 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['158', '159'])).
% 0.20/0.51  thf('161', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('162', plain, ((v8_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('163', plain, ((v3_relat_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('164', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 0.20/0.51  thf('165', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('166', plain, (~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['164', '165'])).
% 0.20/0.51  thf('167', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['157', '166'])).
% 0.20/0.51  thf('168', plain,
% 0.20/0.51      (((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51         (k7_eqrel_1 @ sk_A @ sk_B))
% 0.20/0.51        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['154', '167'])).
% 0.20/0.51  thf('169', plain, (~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['164', '165'])).
% 0.20/0.51  thf('170', plain,
% 0.20/0.51      ((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.51        (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['168', '169'])).
% 0.20/0.51  thf('171', plain,
% 0.20/0.51      ((r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['107', '132', '170'])).
% 0.20/0.51  thf('172', plain, ($false), inference('demod', [status(thm)], ['8', '171'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
