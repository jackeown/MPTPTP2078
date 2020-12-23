%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4KuENVcgR7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:39 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  555 ( 841 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X42 @ X41 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X41 ) @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t129_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X45 ) @ X46 )
      | ( ( k8_relat_1 @ X46 @ X45 )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k8_relat_1 @ X44 @ X43 )
        = ( k5_relat_1 @ X43 @ ( k6_relat_1 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( r1_tarski @ ( k2_relat_1 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( r1_tarski @ X48 @ X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ X0 ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','30'])).

thf('32',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X42 @ X41 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X41 ) @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('36',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X45 ) @ X46 )
      | ( ( k8_relat_1 @ X46 @ X45 )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k8_relat_1 @ X44 @ X43 )
        = ( k5_relat_1 @ X43 @ ( k6_relat_1 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('40',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X51 @ ( k6_relat_1 @ X52 ) ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('41',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['38','47'])).

thf('49',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4KuENVcgR7
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:00:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.79/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.96  % Solved by: fo/fo7.sh
% 0.79/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.96  % done 974 iterations in 0.505s
% 0.79/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.96  % SZS output start Refutation
% 0.79/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/0.96  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.79/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.79/0.96  thf(t119_relat_1, axiom,
% 0.79/0.96    (![A:$i,B:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ B ) =>
% 0.79/0.96       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.79/0.96         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.79/0.96  thf('0', plain,
% 0.79/0.96      (![X41 : $i, X42 : $i]:
% 0.79/0.96         (((k2_relat_1 @ (k8_relat_1 @ X42 @ X41))
% 0.79/0.96            = (k3_xboole_0 @ (k2_relat_1 @ X41) @ X42))
% 0.79/0.96          | ~ (v1_relat_1 @ X41))),
% 0.79/0.96      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.79/0.96  thf(t129_relat_1, conjecture,
% 0.79/0.96    (![A:$i,B:$i,C:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ C ) =>
% 0.79/0.96       ( ( r1_tarski @ A @ B ) =>
% 0.79/0.96         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.79/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.79/0.96        ( ( v1_relat_1 @ C ) =>
% 0.79/0.96          ( ( r1_tarski @ A @ B ) =>
% 0.79/0.96            ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.79/0.96              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.79/0.96    inference('cnf.neg', [status(esa)], [t129_relat_1])).
% 0.79/0.96  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.79/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.96  thf(t71_relat_1, axiom,
% 0.79/0.96    (![A:$i]:
% 0.79/0.96     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.79/0.96       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.79/0.96  thf('2', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.79/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.79/0.96  thf(t125_relat_1, axiom,
% 0.79/0.96    (![A:$i,B:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ B ) =>
% 0.79/0.96       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.79/0.96         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.79/0.96  thf('3', plain,
% 0.79/0.96      (![X45 : $i, X46 : $i]:
% 0.79/0.96         (~ (r1_tarski @ (k2_relat_1 @ X45) @ X46)
% 0.79/0.96          | ((k8_relat_1 @ X46 @ X45) = (X45))
% 0.79/0.96          | ~ (v1_relat_1 @ X45))),
% 0.79/0.96      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.79/0.96  thf('4', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (~ (r1_tarski @ X0 @ X1)
% 0.79/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.79/0.96          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.79/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.79/0.96  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.79/0.96  thf('5', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.79/0.96      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.79/0.96  thf('6', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (~ (r1_tarski @ X0 @ X1)
% 0.79/0.96          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.79/0.96      inference('demod', [status(thm)], ['4', '5'])).
% 0.79/0.96  thf('7', plain,
% 0.79/0.96      (((k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (k6_relat_1 @ sk_A))),
% 0.79/0.96      inference('sup-', [status(thm)], ['1', '6'])).
% 0.79/0.96  thf(t123_relat_1, axiom,
% 0.79/0.96    (![A:$i,B:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ B ) =>
% 0.79/0.96       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.79/0.96  thf('8', plain,
% 0.79/0.96      (![X43 : $i, X44 : $i]:
% 0.79/0.96         (((k8_relat_1 @ X44 @ X43) = (k5_relat_1 @ X43 @ (k6_relat_1 @ X44)))
% 0.79/0.96          | ~ (v1_relat_1 @ X43))),
% 0.79/0.96      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.79/0.96  thf(t76_relat_1, axiom,
% 0.79/0.96    (![A:$i,B:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ B ) =>
% 0.79/0.96       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.79/0.96         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.79/0.96  thf('9', plain,
% 0.79/0.96      (![X51 : $i, X52 : $i]:
% 0.79/0.96         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X52) @ X51) @ X51)
% 0.79/0.96          | ~ (v1_relat_1 @ X51))),
% 0.79/0.96      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.79/0.96  thf('10', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         ((r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.79/0.96           (k6_relat_1 @ X1))
% 0.79/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.79/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.79/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.79/0.96  thf('11', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.79/0.96      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.79/0.96  thf('12', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.79/0.96      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.79/0.96  thf('13', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 0.79/0.96      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.79/0.96  thf('14', plain, ((r1_tarski @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_B))),
% 0.79/0.96      inference('sup+', [status(thm)], ['7', '13'])).
% 0.79/0.96  thf('15', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 0.79/0.96      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.79/0.96  thf(t1_xboole_1, axiom,
% 0.79/0.96    (![A:$i,B:$i,C:$i]:
% 0.79/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.79/0.96       ( r1_tarski @ A @ C ) ))).
% 0.79/0.96  thf('16', plain,
% 0.79/0.96      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.79/0.96         (~ (r1_tarski @ X3 @ X4)
% 0.79/0.96          | ~ (r1_tarski @ X4 @ X5)
% 0.79/0.96          | (r1_tarski @ X3 @ X5))),
% 0.79/0.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.79/0.96  thf('17', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.96         ((r1_tarski @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2)
% 0.79/0.96          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ X2))),
% 0.79/0.96      inference('sup-', [status(thm)], ['15', '16'])).
% 0.79/0.96  thf('18', plain,
% 0.79/0.96      (![X0 : $i]:
% 0.79/0.96         (r1_tarski @ (k8_relat_1 @ sk_A @ (k6_relat_1 @ X0)) @ 
% 0.79/0.96          (k6_relat_1 @ sk_B))),
% 0.79/0.96      inference('sup-', [status(thm)], ['14', '17'])).
% 0.79/0.96  thf(t25_relat_1, axiom,
% 0.79/0.96    (![A:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ A ) =>
% 0.79/0.96       ( ![B:$i]:
% 0.79/0.96         ( ( v1_relat_1 @ B ) =>
% 0.79/0.96           ( ( r1_tarski @ A @ B ) =>
% 0.79/0.96             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.79/0.96               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.79/0.96  thf('19', plain,
% 0.79/0.96      (![X47 : $i, X48 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ X47)
% 0.79/0.96          | (r1_tarski @ (k2_relat_1 @ X48) @ (k2_relat_1 @ X47))
% 0.79/0.96          | ~ (r1_tarski @ X48 @ X47)
% 0.79/0.96          | ~ (v1_relat_1 @ X48))),
% 0.79/0.96      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.79/0.96  thf('20', plain,
% 0.79/0.96      (![X0 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ (k6_relat_1 @ X0)))
% 0.79/0.96          | (r1_tarski @ 
% 0.79/0.96             (k2_relat_1 @ (k8_relat_1 @ sk_A @ (k6_relat_1 @ X0))) @ 
% 0.79/0.96             (k2_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.79/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.79/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.79/0.96  thf('21', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 0.79/0.96      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.79/0.96  thf(t3_subset, axiom,
% 0.79/0.96    (![A:$i,B:$i]:
% 0.79/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.79/0.96  thf('22', plain,
% 0.79/0.96      (![X35 : $i, X37 : $i]:
% 0.79/0.96         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 0.79/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/0.96  thf('23', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (m1_subset_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 0.79/0.96          (k1_zfmisc_1 @ (k6_relat_1 @ X0)))),
% 0.79/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/0.96  thf(cc2_relat_1, axiom,
% 0.79/0.96    (![A:$i]:
% 0.79/0.96     ( ( v1_relat_1 @ A ) =>
% 0.79/0.96       ( ![B:$i]:
% 0.79/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.79/0.96  thf('24', plain,
% 0.79/0.96      (![X38 : $i, X39 : $i]:
% 0.79/0.96         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.79/0.96          | (v1_relat_1 @ X38)
% 0.79/0.96          | ~ (v1_relat_1 @ X39))),
% 0.79/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.96  thf('25', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.79/0.96          | (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.79/0.96      inference('sup-', [status(thm)], ['23', '24'])).
% 0.79/0.96  thf('26', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.79/0.96      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.79/0.96  thf('27', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.79/0.96      inference('demod', [status(thm)], ['25', '26'])).
% 0.79/0.96  thf('28', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.79/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.79/0.96  thf('29', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.79/0.96      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.79/0.96  thf('30', plain,
% 0.79/0.96      (![X0 : $i]:
% 0.79/0.96         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ (k6_relat_1 @ X0))) @ 
% 0.79/0.96          sk_B)),
% 0.79/0.96      inference('demod', [status(thm)], ['20', '27', '28', '29'])).
% 0.79/0.96  thf('31', plain,
% 0.79/0.96      (![X0 : $i]:
% 0.79/0.96         ((r1_tarski @ 
% 0.79/0.96           (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ sk_A) @ sk_B)
% 0.79/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.79/0.96      inference('sup+', [status(thm)], ['0', '30'])).
% 0.79/0.96  thf('32', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.79/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.79/0.96  thf('33', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.79/0.96      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.79/0.96  thf('34', plain,
% 0.79/0.96      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.79/0.96      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.79/0.96  thf('35', plain,
% 0.79/0.96      (![X41 : $i, X42 : $i]:
% 0.79/0.96         (((k2_relat_1 @ (k8_relat_1 @ X42 @ X41))
% 0.79/0.96            = (k3_xboole_0 @ (k2_relat_1 @ X41) @ X42))
% 0.79/0.96          | ~ (v1_relat_1 @ X41))),
% 0.79/0.96      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.79/0.96  thf('36', plain,
% 0.79/0.96      (![X45 : $i, X46 : $i]:
% 0.79/0.96         (~ (r1_tarski @ (k2_relat_1 @ X45) @ X46)
% 0.79/0.96          | ((k8_relat_1 @ X46 @ X45) = (X45))
% 0.79/0.96          | ~ (v1_relat_1 @ X45))),
% 0.79/0.96      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.79/0.96  thf('37', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.96         (~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2)
% 0.79/0.96          | ~ (v1_relat_1 @ X1)
% 0.79/0.96          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.79/0.96          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))
% 0.79/0.96              = (k8_relat_1 @ X0 @ X1)))),
% 0.79/0.96      inference('sup-', [status(thm)], ['35', '36'])).
% 0.79/0.96  thf('38', plain,
% 0.79/0.96      (![X0 : $i]:
% 0.79/0.96         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.79/0.96            = (k8_relat_1 @ sk_A @ X0))
% 0.79/0.96          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.79/0.96          | ~ (v1_relat_1 @ X0))),
% 0.79/0.96      inference('sup-', [status(thm)], ['34', '37'])).
% 0.79/0.96  thf('39', plain,
% 0.79/0.96      (![X43 : $i, X44 : $i]:
% 0.79/0.96         (((k8_relat_1 @ X44 @ X43) = (k5_relat_1 @ X43 @ (k6_relat_1 @ X44)))
% 0.79/0.96          | ~ (v1_relat_1 @ X43))),
% 0.79/0.96      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.79/0.96  thf('40', plain,
% 0.79/0.96      (![X51 : $i, X52 : $i]:
% 0.79/0.96         ((r1_tarski @ (k5_relat_1 @ X51 @ (k6_relat_1 @ X52)) @ X51)
% 0.79/0.96          | ~ (v1_relat_1 @ X51))),
% 0.79/0.96      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.79/0.96  thf('41', plain,
% 0.79/0.96      (![X35 : $i, X37 : $i]:
% 0.79/0.96         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 0.79/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/0.96  thf('42', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ X0)
% 0.79/0.96          | (m1_subset_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 0.79/0.96             (k1_zfmisc_1 @ X0)))),
% 0.79/0.96      inference('sup-', [status(thm)], ['40', '41'])).
% 0.79/0.96  thf('43', plain,
% 0.79/0.96      (![X38 : $i, X39 : $i]:
% 0.79/0.96         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.79/0.96          | (v1_relat_1 @ X38)
% 0.79/0.96          | ~ (v1_relat_1 @ X39))),
% 0.79/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.96  thf('44', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ X0)
% 0.79/0.96          | ~ (v1_relat_1 @ X0)
% 0.79/0.96          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.79/0.96      inference('sup-', [status(thm)], ['42', '43'])).
% 0.79/0.96  thf('45', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.79/0.96          | ~ (v1_relat_1 @ X0))),
% 0.79/0.96      inference('simplify', [status(thm)], ['44'])).
% 0.79/0.96  thf('46', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.79/0.96          | ~ (v1_relat_1 @ X0)
% 0.79/0.96          | ~ (v1_relat_1 @ X0))),
% 0.79/0.96      inference('sup+', [status(thm)], ['39', '45'])).
% 0.79/0.96  thf('47', plain,
% 0.79/0.96      (![X0 : $i, X1 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.79/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.79/0.96  thf('48', plain,
% 0.79/0.96      (![X0 : $i]:
% 0.79/0.96         (~ (v1_relat_1 @ X0)
% 0.79/0.96          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.79/0.96              = (k8_relat_1 @ sk_A @ X0)))),
% 0.79/0.96      inference('clc', [status(thm)], ['38', '47'])).
% 0.79/0.96  thf('49', plain,
% 0.79/0.96      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.79/0.96         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.79/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.96  thf('50', plain,
% 0.79/0.96      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.79/0.96        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.96      inference('sup-', [status(thm)], ['48', '49'])).
% 0.79/0.96  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.96  thf('52', plain,
% 0.79/0.96      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.79/0.96      inference('demod', [status(thm)], ['50', '51'])).
% 0.79/0.96  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.79/0.96  
% 0.79/0.96  % SZS output end Refutation
% 0.79/0.96  
% 0.79/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
