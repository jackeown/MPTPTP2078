%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EEygJWiP0a

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 703 expanded)
%              Number of leaves         :   36 ( 221 expanded)
%              Depth                    :   15
%              Number of atoms          : 2236 (15068 expanded)
%              Number of equality atoms :   13 (  40 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(k7_eqrel_1_type,type,(
    k7_eqrel_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k8_eqrel_1 @ X25 @ X26 )
        = ( k7_eqrel_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) )
      | ~ ( v1_partfun1 @ X26 @ X25 )
      | ~ ( v8_relat_2 @ X26 )
      | ~ ( v3_relat_2 @ X26 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( m2_filter_1 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ~ ( r3_binop_1 @ X10 @ X11 @ X9 )
      | ( r2_binop_1 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_funct_2 @ X22 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( m2_filter_1 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_funct_1 @ X22 )
      | ~ ( m2_filter_1 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('30',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','27','34'])).

thf('36',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X32 )
      | ~ ( v3_relat_2 @ X31 )
      | ~ ( v8_relat_2 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( m2_filter_1 @ X33 @ X32 @ X31 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ X32 @ X31 ) @ ( k9_eqrel_1 @ X32 @ X31 @ X34 ) @ ( k3_filter_1 @ X32 @ X31 @ X33 ) )
      | ~ ( r2_binop_1 @ X32 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_filter_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('44',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

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

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) )
      | ~ ( v8_relat_2 @ X12 )
      | ~ ( v3_relat_2 @ X12 )
      | ~ ( v1_partfun1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X13 @ X12 ) @ ( k8_eqrel_1 @ X13 @ X12 ) ) @ ( k8_eqrel_1 @ X13 @ X12 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['32','33'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('66',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('67',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ~ ( r1_binop_1 @ X10 @ X11 @ X9 )
      | ~ ( r2_binop_1 @ X10 @ X11 @ X9 )
      | ( r3_binop_1 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('75',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) )
      | ~ ( v8_relat_2 @ X12 )
      | ~ ( v3_relat_2 @ X12 )
      | ~ ( v1_partfun1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X13 @ X12 @ X14 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X13 @ X12 ) @ ( k8_eqrel_1 @ X13 @ X12 ) ) @ ( k8_eqrel_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['32','33'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('85',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('86',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('92',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) )
      | ~ ( v8_relat_2 @ X12 )
      | ~ ( v3_relat_2 @ X12 )
      | ~ ( v1_partfun1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
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
    inference(clc,[status(thm)],['25','26'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['32','33'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
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
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
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
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','89','103'])).

thf('105',plain,
    ( ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','104'])).

thf('106',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('108',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) @ X10 ) ) )
      | ~ ( r3_binop_1 @ X10 @ X11 @ X9 )
      | ( r1_binop_1 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['32','33'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r1_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
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

thf('118',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v3_relat_2 @ X27 )
      | ~ ( v8_relat_2 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( m2_filter_1 @ X29 @ X28 @ X27 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ X28 @ X27 ) @ ( k9_eqrel_1 @ X28 @ X27 @ X30 ) @ ( k3_filter_1 @ X28 @ X27 @ X29 ) )
      | ~ ( r1_binop_1 @ X28 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('121',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['115','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
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

thf('133',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v8_relat_2 @ X17 )
      | ~ ( v3_relat_2 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X18 @ X17 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) @ ( k8_eqrel_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B )
    = ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('136',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['131','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( m1_subset_1 @ ( k7_eqrel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('144',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k7_eqrel_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) )
      | ~ ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v8_relat_2 @ X16 )
      | ~ ( v3_relat_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_eqrel_1])).

thf('145',plain,
    ( ~ ( v3_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('150',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X8 @ X6 )
      | ~ ( m2_subset_1 @ X8 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('155',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
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

thf('157',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v3_relat_2 @ X24 )
      | ~ ( v8_relat_2 @ X24 )
      | ~ ( v1_partfun1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) )
      | ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_eqrel_1])).

thf('158',plain,
    ( ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','164'])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['152','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('168',plain,(
    m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['105','130','168'])).

thf('170',plain,(
    $false ),
    inference(demod,[status(thm)],['8','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EEygJWiP0a
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 72 iterations in 0.053s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r3_binop_1_type, type, r3_binop_1: $i > $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k9_eqrel_1_type, type, k9_eqrel_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(r2_binop_1_type, type, r2_binop_1: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k8_eqrel_1_type, type, k8_eqrel_1: $i > $i > $i).
% 0.21/0.52  thf(k3_filter_1_type, type, k3_filter_1: $i > $i > $i > $i).
% 0.21/0.52  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.21/0.52  thf(k7_eqrel_1_type, type, k7_eqrel_1: $i > $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(r1_binop_1_type, type, r1_binop_1: $i > $i > $i > $o).
% 0.21/0.52  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(m2_filter_1_type, type, m2_filter_1: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.52  thf(m2_subset_1_type, type, m2_subset_1: $i > $i > $i > $o).
% 0.21/0.52  thf(t8_filter_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.52             ( v8_relat_2 @ B ) & 
% 0.21/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.52                   ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.21/0.52                     ( r3_binop_1 @
% 0.21/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.21/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.52                ( v8_relat_2 @ B ) & 
% 0.21/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.52                      ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.21/0.52                        ( r3_binop_1 @
% 0.21/0.52                          ( k8_eqrel_1 @ A @ B ) @ 
% 0.21/0.52                          ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.21/0.52                          ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t8_filter_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k8_eqrel_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52       ( ( k8_eqrel_1 @ A @ B ) = ( k7_eqrel_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X25 : $i, X26 : $i]:
% 0.21/0.52         (((k8_eqrel_1 @ X25 @ X26) = (k7_eqrel_1 @ X25 @ X26))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))
% 0.21/0.52          | ~ (v1_partfun1 @ X26 @ X25)
% 0.21/0.52          | ~ (v8_relat_2 @ X26)
% 0.21/0.52          | ~ (v3_relat_2 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k8_eqrel_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      ((~ (v3_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.52        | ((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (~ (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.52  thf('9', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m2_filter_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.21/0.52           ( ( v1_funct_1 @ C ) & 
% 0.21/0.52             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.52             ( m1_subset_1 @
% 0.21/0.52               C @ 
% 0.21/0.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X20)
% 0.21/0.52          | ~ (v1_relat_1 @ X21)
% 0.21/0.52          | (m1_subset_1 @ X22 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)))
% 0.21/0.52          | ~ (m2_filter_1 @ X22 @ X20 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_D @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( v1_relat_1 @ C ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((v1_relat_1 @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.52  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_D @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.52  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf(d7_binop_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.52             ( m1_subset_1 @
% 0.21/0.52               C @ 
% 0.21/0.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.21/0.52           ( ( r3_binop_1 @ A @ B @ C ) <=>
% 0.21/0.52             ( ( r1_binop_1 @ A @ B @ C ) & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X9)
% 0.21/0.52          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 0.21/0.52          | ~ (r3_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | (r2_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X20)
% 0.21/0.52          | ~ (v1_relat_1 @ X21)
% 0.21/0.52          | (v1_funct_2 @ X22 @ (k2_zfmisc_1 @ X20 @ X20) @ X20)
% 0.21/0.52          | ~ (m2_filter_1 @ X22 @ X20 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X20)
% 0.21/0.52          | ~ (v1_relat_1 @ X21)
% 0.21/0.52          | (v1_funct_1 @ X22)
% 0.21/0.52          | ~ (m2_filter_1 @ X22 @ X20 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('32', plain, (((v1_funct_1 @ sk_D) | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '27', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((r2_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '35'])).
% 0.21/0.52  thf('37', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain, ((r2_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t7_filter_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.52             ( v8_relat_2 @ B ) & 
% 0.21/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.52                   ( ( r2_binop_1 @ A @ C @ D ) =>
% 0.21/0.52                     ( r2_binop_1 @
% 0.21/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.21/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.52         (~ (v1_partfun1 @ X31 @ X32)
% 0.21/0.52          | ~ (v3_relat_2 @ X31)
% 0.21/0.52          | ~ (v8_relat_2 @ X31)
% 0.21/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.21/0.52          | ~ (m2_filter_1 @ X33 @ X32 @ X31)
% 0.21/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ X32 @ X31) @ 
% 0.21/0.52             (k9_eqrel_1 @ X32 @ X31 @ X34) @ (k3_filter_1 @ X32 @ X31 @ X33))
% 0.21/0.52          | ~ (r2_binop_1 @ X32 @ X34 @ X33)
% 0.21/0.52          | ~ (m1_subset_1 @ X34 @ X32)
% 0.21/0.52          | (v1_xboole_0 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_filter_1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.21/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('44', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.52          | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.21/0.52        | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '48'])).
% 0.21/0.52  thf('50', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      ((r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf(dt_k3_filter_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_partfun1 @ B @ A ) & 
% 0.21/0.52         ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.52         ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.21/0.52         ( m1_subset_1 @
% 0.21/0.52           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.21/0.52       ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) ) & 
% 0.21/0.52         ( v1_funct_2 @
% 0.21/0.52           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.52           ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.21/0.52           ( k8_eqrel_1 @ A @ B ) ) & 
% 0.21/0.52         ( m1_subset_1 @
% 0.21/0.52           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.21/0.52           ( k1_zfmisc_1 @
% 0.21/0.52             ( k2_zfmisc_1 @
% 0.21/0.52               ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.21/0.52               ( k8_eqrel_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))
% 0.21/0.52          | ~ (v8_relat_2 @ X12)
% 0.21/0.52          | ~ (v3_relat_2 @ X12)
% 0.21/0.52          | ~ (v1_partfun1 @ X12 @ X13)
% 0.21/0.52          | (v1_xboole_0 @ X13)
% 0.21/0.52          | ~ (v1_funct_1 @ X14)
% 0.21/0.52          | ~ (v1_funct_2 @ X14 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)))
% 0.21/0.52          | (m1_subset_1 @ (k3_filter_1 @ X13 @ X12 @ X14) @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k8_eqrel_1 @ X13 @ X12) @ 
% 0.21/0.52                (k8_eqrel_1 @ X13 @ X12)) @ 
% 0.21/0.52               (k8_eqrel_1 @ X13 @ X12)))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.52           (k1_zfmisc_1 @ 
% 0.21/0.52            (k2_zfmisc_1 @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.52             (k8_eqrel_1 @ sk_A @ X0))))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.52           (k1_zfmisc_1 @ 
% 0.21/0.52            (k2_zfmisc_1 @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.52             (k8_eqrel_1 @ sk_A @ X0))))
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52           (k1_zfmisc_1 @ 
% 0.21/0.52            (k2_zfmisc_1 @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '60'])).
% 0.21/0.52  thf('62', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('66', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('67', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52           (k1_zfmisc_1 @ 
% 0.21/0.52            (k2_zfmisc_1 @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52              (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52             (k7_eqrel_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['61', '62', '63', '64', '65', '66', '67'])).
% 0.21/0.52  thf('69', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ 
% 0.21/0.52          (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52          (k7_eqrel_1 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X9)
% 0.21/0.52          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 0.21/0.52          | ~ (r1_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | ~ (r2_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | (r3_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52                (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52               (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))
% 0.21/0.52          | ~ (v8_relat_2 @ X12)
% 0.21/0.52          | ~ (v3_relat_2 @ X12)
% 0.21/0.52          | ~ (v1_partfun1 @ X12 @ X13)
% 0.21/0.52          | (v1_xboole_0 @ X13)
% 0.21/0.52          | ~ (v1_funct_1 @ X14)
% 0.21/0.52          | ~ (v1_funct_2 @ X14 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)))
% 0.21/0.52          | (v1_funct_2 @ (k3_filter_1 @ X13 @ X12 @ X14) @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ X13 @ X12) @ (k8_eqrel_1 @ X13 @ X12)) @ 
% 0.21/0.52             (k8_eqrel_1 @ X13 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.52           (k8_eqrel_1 @ sk_A @ X0))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.21/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.21/0.52           (k8_eqrel_1 @ sk_A @ X0))
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ sk_A)
% 0.21/0.52        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '79'])).
% 0.21/0.52  thf('81', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('82', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('83', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('84', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('85', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('86', plain, (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52           (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52            (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52           (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['80', '81', '82', '83', '84', '85', '86'])).
% 0.21/0.52  thf('88', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.21/0.52        (k2_zfmisc_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ (k7_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.21/0.52        (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))
% 0.21/0.52          | ~ (v8_relat_2 @ X12)
% 0.21/0.52          | ~ (v3_relat_2 @ X12)
% 0.21/0.52          | ~ (v1_partfun1 @ X12 @ X13)
% 0.21/0.52          | (v1_xboole_0 @ X13)
% 0.21/0.52          | ~ (v1_funct_1 @ X14)
% 0.21/0.52          | ~ (v1_funct_2 @ X14 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)))
% 0.21/0.52          | (v1_funct_1 @ (k3_filter_1 @ X13 @ X12 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.52  thf('94', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ sk_A)
% 0.21/0.52        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['90', '96'])).
% 0.21/0.52  thf('98', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('100', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('101', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.21/0.52  thf('102', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('103', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['101', '102'])).
% 0.21/0.52  thf('104', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (r2_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '89', '103'])).
% 0.21/0.52  thf('105', plain,
% 0.21/0.52      ((~ (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52        | (r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52        | ~ (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52             (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['53', '104'])).
% 0.21/0.52  thf('106', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('107', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X9)
% 0.21/0.52          | ~ (v1_funct_2 @ X9 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10) @ X10)))
% 0.21/0.52          | ~ (r3_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | (r1_binop_1 @ X10 @ X11 @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.21/0.52  thf('109', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.21/0.52  thf('110', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('112', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.21/0.52  thf('113', plain,
% 0.21/0.52      (((r1_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['106', '112'])).
% 0.21/0.52  thf('114', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('115', plain, ((r1_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['113', '114'])).
% 0.21/0.52  thf('116', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('117', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t6_filter_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.21/0.52             ( v8_relat_2 @ B ) & 
% 0.21/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.21/0.52                   ( ( r1_binop_1 @ A @ C @ D ) =>
% 0.21/0.52                     ( r1_binop_1 @
% 0.21/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.21/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('118', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (v1_partfun1 @ X27 @ X28)
% 0.21/0.52          | ~ (v3_relat_2 @ X27)
% 0.21/0.52          | ~ (v8_relat_2 @ X27)
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.21/0.52          | ~ (m2_filter_1 @ X29 @ X28 @ X27)
% 0.21/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ X28 @ X27) @ 
% 0.21/0.52             (k9_eqrel_1 @ X28 @ X27 @ X30) @ (k3_filter_1 @ X28 @ X27 @ X29))
% 0.21/0.52          | ~ (r1_binop_1 @ X28 @ X30 @ X29)
% 0.21/0.52          | ~ (m1_subset_1 @ X30 @ X28)
% 0.21/0.52          | (v1_xboole_0 @ X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [t6_filter_1])).
% 0.21/0.52  thf('119', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.21/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.52  thf('120', plain,
% 0.21/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('121', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('122', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('123', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('124', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.21/0.52          | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.21/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.21/0.52  thf('125', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['116', '124'])).
% 0.21/0.52  thf('126', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.21/0.52        | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['115', '125'])).
% 0.21/0.52  thf('127', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('128', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | (r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['126', '127'])).
% 0.21/0.52  thf('129', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('130', plain,
% 0.21/0.52      ((r1_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['128', '129'])).
% 0.21/0.52  thf('131', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('132', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k9_eqrel_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.21/0.52         ( v1_partfun1 @ B @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ A ) ) =>
% 0.21/0.52       ( m2_subset_1 @
% 0.21/0.52         ( k9_eqrel_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) @ 
% 0.21/0.52         ( k8_eqrel_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('133', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.21/0.52          | ~ (v1_partfun1 @ X17 @ X18)
% 0.21/0.52          | ~ (v8_relat_2 @ X17)
% 0.21/0.52          | ~ (v3_relat_2 @ X17)
% 0.21/0.52          | (v1_xboole_0 @ X18)
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ X18)
% 0.21/0.52          | (m2_subset_1 @ (k9_eqrel_1 @ X18 @ X17 @ X19) @ 
% 0.21/0.52             (k1_zfmisc_1 @ X18) @ (k8_eqrel_1 @ X18 @ X17)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k9_eqrel_1])).
% 0.21/0.52  thf('134', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.52           (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['132', '133'])).
% 0.21/0.52  thf('135', plain,
% 0.21/0.52      (((k8_eqrel_1 @ sk_A @ sk_B) = (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.52  thf('136', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('137', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('138', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('139', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.52           (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.21/0.52  thf('140', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('141', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('clc', [status(thm)], ['139', '140'])).
% 0.21/0.52  thf('142', plain,
% 0.21/0.52      ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ sk_A) @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['131', '141'])).
% 0.21/0.52  thf('143', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k7_eqrel_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k7_eqrel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.52  thf('144', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k7_eqrel_1 @ X15 @ X16) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))
% 0.21/0.52          | ~ (v1_partfun1 @ X16 @ X15)
% 0.21/0.52          | ~ (v8_relat_2 @ X16)
% 0.21/0.52          | ~ (v3_relat_2 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_eqrel_1])).
% 0.21/0.52  thf('145', plain,
% 0.21/0.52      ((~ (v3_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['143', '144'])).
% 0.21/0.52  thf('146', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('147', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('148', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('149', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.21/0.52  thf(redefinition_m2_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.52       ( ![C:$i]: ( ( m2_subset_1 @ C @ A @ B ) <=> ( m1_subset_1 @ C @ B ) ) ) ))).
% 0.21/0.52  thf('150', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X5)
% 0.21/0.52          | (v1_xboole_0 @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 0.21/0.52          | (m1_subset_1 @ X8 @ X6)
% 0.21/0.52          | ~ (m2_subset_1 @ X8 @ X5 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.21/0.52  thf('151', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.21/0.52             (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | (m1_subset_1 @ X0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['149', '150'])).
% 0.21/0.52  thf('152', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.52        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52        | (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52           (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['142', '151'])).
% 0.21/0.52  thf('153', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.21/0.52  thf(cc1_subset_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.52  thf('154', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.52          | (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.52  thf('155', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.52        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['153', '154'])).
% 0.21/0.52  thf('156', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(fc3_eqrel_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.21/0.52         ( v1_partfun1 @ B @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( k7_eqrel_1 @ A @ B ) ) ) ))).
% 0.21/0.52  thf('157', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X23)
% 0.21/0.52          | ~ (v3_relat_2 @ X24)
% 0.21/0.52          | ~ (v8_relat_2 @ X24)
% 0.21/0.52          | ~ (v1_partfun1 @ X24 @ X23)
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k7_eqrel_1 @ X23 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc3_eqrel_1])).
% 0.21/0.52  thf('158', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['156', '157'])).
% 0.21/0.52  thf('159', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('160', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('161', plain, ((v3_relat_2 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('162', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 0.21/0.52  thf('163', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('164', plain, (~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['162', '163'])).
% 0.21/0.52  thf('165', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['155', '164'])).
% 0.21/0.52  thf('166', plain,
% 0.21/0.52      (((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52         (k7_eqrel_1 @ sk_A @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('clc', [status(thm)], ['152', '165'])).
% 0.21/0.52  thf('167', plain, (~ (v1_xboole_0 @ (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['162', '163'])).
% 0.21/0.52  thf('168', plain,
% 0.21/0.52      ((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.52        (k7_eqrel_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['166', '167'])).
% 0.21/0.52  thf('169', plain,
% 0.21/0.52      ((r3_binop_1 @ (k7_eqrel_1 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['105', '130', '168'])).
% 0.21/0.52  thf('170', plain, ($false), inference('demod', [status(thm)], ['8', '169'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
