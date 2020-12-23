%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSSC8v2ZCy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:55 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 163 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  548 (1329 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X23: $i] :
      ( ( r1_tarski @ X23 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X23 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X4 ) @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) @ X19 ) ),
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
    ! [X23: $i] :
      ( ( r1_tarski @ X23 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X23 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X4 ) @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) @ X22 ) ),
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
    ! [X16: $i] :
      ( ( ( k3_relat_1 @ X16 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k3_relat_1 @ X25 ) @ ( k3_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('43',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf('47',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['5','42','45','46'])).

thf(t63_relat_1,axiom,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('48',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t63_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSSC8v2ZCy
% 0.14/0.38  % Computer   : n015.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 12:29:53 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 114 iterations in 0.068s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.24/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.56  thf(t19_relset_1, conjecture,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.56       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.56          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.24/0.56  thf('0', plain,
% 0.24/0.56      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(t3_subset, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.56  thf('2', plain,
% 0.24/0.56      (![X8 : $i, X9 : $i]:
% 0.24/0.56         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.56  thf('3', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.56  thf(d10_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      (![X0 : $i, X2 : $i]:
% 0.24/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('5', plain,
% 0.24/0.56      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.24/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.56  thf(t21_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( r1_tarski @
% 0.24/0.56         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.24/0.56  thf('6', plain,
% 0.24/0.56      (![X23 : $i]:
% 0.24/0.56         ((r1_tarski @ X23 @ 
% 0.24/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ X23) @ (k2_relat_1 @ X23)))
% 0.24/0.56          | ~ (v1_relat_1 @ X23))),
% 0.24/0.56      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.24/0.56  thf(t138_zfmisc_1, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.56     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.24/0.56       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.56         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.24/0.56  thf('7', plain,
% 0.24/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.56         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0))
% 0.24/0.56          | ~ (r1_tarski @ (k2_zfmisc_1 @ X3 @ X4) @ (k2_zfmisc_1 @ X5 @ X6))
% 0.24/0.56          | (r1_tarski @ X3 @ X5))),
% 0.24/0.56      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.24/0.56  thf('8', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.24/0.56          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.24/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.56  thf(fc6_relat_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.56  thf('9', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.56  thf('10', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.24/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf(t193_relat_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.24/0.56  thf('11', plain,
% 0.24/0.56      (![X19 : $i, X20 : $i]:
% 0.24/0.56         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20)) @ X19)),
% 0.24/0.56      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      (![X0 : $i, X2 : $i]:
% 0.24/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.24/0.56          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.24/0.56          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['10', '13'])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      (![X23 : $i]:
% 0.24/0.56         ((r1_tarski @ X23 @ 
% 0.24/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ X23) @ (k2_relat_1 @ X23)))
% 0.24/0.56          | ~ (v1_relat_1 @ X23))),
% 0.24/0.56      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.24/0.56  thf('16', plain,
% 0.24/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.56         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0))
% 0.24/0.56          | ~ (r1_tarski @ (k2_zfmisc_1 @ X3 @ X4) @ (k2_zfmisc_1 @ X5 @ X6))
% 0.24/0.56          | (r1_tarski @ X4 @ X6))),
% 0.24/0.56      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.24/0.56          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.24/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.56  thf('19', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.24/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.24/0.56  thf(t194_relat_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (![X21 : $i, X22 : $i]:
% 0.24/0.56         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X21 @ X22)) @ X22)),
% 0.24/0.56      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (![X0 : $i, X2 : $i]:
% 0.24/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('22', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.24/0.56          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.24/0.56          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['19', '22'])).
% 0.24/0.56  thf(d6_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ( k3_relat_1 @ A ) =
% 0.24/0.56         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.24/0.56  thf('24', plain,
% 0.24/0.56      (![X16 : $i]:
% 0.24/0.56         (((k3_relat_1 @ X16)
% 0.24/0.56            = (k2_xboole_0 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.24/0.56          | ~ (v1_relat_1 @ X16))),
% 0.24/0.56      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.24/0.56  thf('25', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k3_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.24/0.56            = (k2_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))
% 0.24/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.24/0.56          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.24/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.24/0.56  thf('26', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k3_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.24/0.56            = (k2_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))
% 0.24/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.24/0.56  thf('28', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k3_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k2_xboole_0 @ X0 @ X1))
% 0.24/0.56          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.24/0.56          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup+', [status(thm)], ['14', '27'])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.24/0.56          | ((k3_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k2_xboole_0 @ X0 @ X1)))),
% 0.24/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.24/0.56  thf('30', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.56  thf(t31_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( v1_relat_1 @ B ) =>
% 0.24/0.56           ( ( r1_tarski @ A @ B ) =>
% 0.24/0.56             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.24/0.56  thf('31', plain,
% 0.24/0.56      (![X24 : $i, X25 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X24)
% 0.24/0.56          | (r1_tarski @ (k3_relat_1 @ X25) @ (k3_relat_1 @ X24))
% 0.24/0.56          | ~ (r1_tarski @ X25 @ X24)
% 0.24/0.56          | ~ (v1_relat_1 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.24/0.56  thf('32', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.56        | (r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.24/0.56           (k3_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.24/0.56        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.56  thf('33', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(cc2_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.56  thf('34', plain,
% 0.24/0.56      (![X14 : $i, X15 : $i]:
% 0.24/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.24/0.56          | (v1_relat_1 @ X14)
% 0.24/0.56          | ~ (v1_relat_1 @ X15))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.24/0.56  thf('36', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.56  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.24/0.56  thf('38', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.56  thf('39', plain,
% 0.24/0.56      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.24/0.56        (k3_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.56      inference('demod', [status(thm)], ['32', '37', '38'])).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.24/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup+', [status(thm)], ['29', '39'])).
% 0.24/0.56  thf('41', plain,
% 0.24/0.56      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('42', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.56      inference('clc', [status(thm)], ['40', '41'])).
% 0.24/0.56  thf(t4_subset_1, axiom,
% 0.24/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.56  thf('43', plain,
% 0.24/0.56      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.56  thf('44', plain,
% 0.24/0.56      (![X8 : $i, X9 : $i]:
% 0.24/0.56         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.56  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.24/0.56  thf('46', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.56      inference('clc', [status(thm)], ['40', '41'])).
% 0.24/0.56  thf('47', plain, (((k1_xboole_0) = (sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['5', '42', '45', '46'])).
% 0.24/0.56  thf(t63_relat_1, axiom, (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.24/0.56  thf('48', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [t63_relat_1])).
% 0.24/0.56  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.24/0.56  thf('50', plain, ($false),
% 0.24/0.56      inference('demod', [status(thm)], ['0', '47', '48', '49'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
