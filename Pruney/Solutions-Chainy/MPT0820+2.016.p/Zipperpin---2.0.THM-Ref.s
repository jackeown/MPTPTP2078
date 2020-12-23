%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EvcMU7QD6u

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:50 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 166 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  564 (1357 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X30: $i] :
      ( ( r1_tarski @ X30 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X14 @ X15 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) @ X26 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X30: $i] :
      ( ( r1_tarski @ X30 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X14 @ X15 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) @ X29 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X21: $i] :
      ( ( ( k3_relat_1 @ X21 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X21 ) @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k3_relat_1 @ X34 ) @ ( k3_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('48',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['5','40','46','47'])).

thf(t63_relat_1,axiom,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('49',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t63_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48','49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EvcMU7QD6u
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 476 iterations in 0.486s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.98  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.76/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(t19_relset_1, conjecture,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.98        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t3_subset, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      (![X18 : $i, X19 : $i]:
% 0.76/0.98         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.98  thf('3', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.98  thf(d10_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      (![X0 : $i, X2 : $i]:
% 0.76/0.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.76/0.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.98  thf(t21_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( r1_tarski @
% 0.76/0.98         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      (![X30 : $i]:
% 0.76/0.98         ((r1_tarski @ X30 @ 
% 0.76/0.98           (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30)))
% 0.76/0.98          | ~ (v1_relat_1 @ X30))),
% 0.76/0.98      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.76/0.98  thf(t138_zfmisc_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.76/0.98       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.76/0.98         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.98         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.76/0.98          | ~ (r1_tarski @ (k2_zfmisc_1 @ X14 @ X15) @ 
% 0.76/0.98               (k2_zfmisc_1 @ X16 @ X17))
% 0.76/0.98          | (r1_tarski @ X14 @ X16))),
% 0.76/0.98      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.76/0.98          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('9', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['8', '9'])).
% 0.76/0.98  thf(t193_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i]:
% 0.76/0.98         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27)) @ X26)),
% 0.76/0.98      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      (![X0 : $i, X2 : $i]:
% 0.76/0.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.76/0.98          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.98          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['10', '13'])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (![X30 : $i]:
% 0.76/0.98         ((r1_tarski @ X30 @ 
% 0.76/0.98           (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30)))
% 0.76/0.98          | ~ (v1_relat_1 @ X30))),
% 0.76/0.98      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.98         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.76/0.98          | ~ (r1_tarski @ (k2_zfmisc_1 @ X14 @ X15) @ 
% 0.76/0.98               (k2_zfmisc_1 @ X16 @ X17))
% 0.76/0.98          | (r1_tarski @ X15 @ X17))),
% 0.76/0.98      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.76/0.98          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.98  thf(t194_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      (![X28 : $i, X29 : $i]:
% 0.76/0.98         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X28 @ X29)) @ X29)),
% 0.76/0.98      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X0 : $i, X2 : $i]:
% 0.76/0.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.98          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['19', '22'])).
% 0.76/0.98  thf(d6_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ( k3_relat_1 @ A ) =
% 0.76/0.98         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X21 : $i]:
% 0.76/0.98         (((k3_relat_1 @ X21)
% 0.76/0.98            = (k2_xboole_0 @ (k1_relat_1 @ X21) @ (k2_relat_1 @ X21)))
% 0.76/0.98          | ~ (v1_relat_1 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k3_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.76/0.98            = (k2_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))
% 0.76/0.98          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['23', '24'])).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k3_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.76/0.98            = (k2_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))
% 0.76/0.98          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['25', '26'])).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k3_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k2_xboole_0 @ X0 @ X1))
% 0.76/0.98          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.76/0.98          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['14', '27'])).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.76/0.98          | ((k3_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k2_xboole_0 @ X0 @ X1)))),
% 0.76/0.98      inference('simplify', [status(thm)], ['28'])).
% 0.76/0.98  thf('30', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.98  thf(t31_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( v1_relat_1 @ B ) =>
% 0.76/0.98           ( ( r1_tarski @ A @ B ) =>
% 0.76/0.98             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (![X33 : $i, X34 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X33)
% 0.76/0.98          | (r1_tarski @ (k3_relat_1 @ X34) @ (k3_relat_1 @ X33))
% 0.76/0.98          | ~ (r1_tarski @ X34 @ X33)
% 0.76/0.98          | ~ (v1_relat_1 @ X34))),
% 0.76/0.98      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.98        | (r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.76/0.98           (k3_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.76/0.98        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc1_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( v1_relat_1 @ C ) ))).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.76/0.98         ((v1_relat_1 @ X35)
% 0.76/0.98          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.98  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.76/0.98        (k3_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.76/0.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['29', '37'])).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('40', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.76/0.98      inference('clc', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('41', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.98      inference('simplify', [status(thm)], ['41'])).
% 0.76/0.98  thf(t2_boole, axiom,
% 0.76/0.98    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.98  thf(t18_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.98         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X1 @ k1_xboole_0) | (r1_tarski @ X1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.98  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['42', '45'])).
% 0.76/0.98  thf('47', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.76/0.98      inference('clc', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('48', plain, (((k1_xboole_0) = (sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['5', '40', '46', '47'])).
% 0.76/0.98  thf(t63_relat_1, axiom, (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.76/0.98  thf('49', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t63_relat_1])).
% 0.76/0.98  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['42', '45'])).
% 0.76/0.98  thf('51', plain, ($false),
% 0.76/0.98      inference('demod', [status(thm)], ['0', '48', '49', '50'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
