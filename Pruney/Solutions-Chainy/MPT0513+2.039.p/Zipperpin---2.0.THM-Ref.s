%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5qeQLHSGFj

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:30 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 265 expanded)
%              Number of leaves         :   30 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  447 (1814 expanded)
%              Number of equality atoms :   56 ( 191 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X51: $i] :
      ( ( ( k7_relat_1 @ X51 @ ( k1_relat_1 @ X51 ) )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('3',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X45: $i] :
      ( ( v1_relat_1 @ X45 )
      | ( r2_hidden @ ( sk_B @ X45 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('8',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k1_tarski @ ( sk_B @ k1_xboole_0 ) ) )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,
    ( ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('27',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('28',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('29',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('30',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
     != ( k1_tarski @ ( sk_B @ k1_xboole_0 ) ) )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k1_tarski @ ( sk_B @ k1_xboole_0 ) ) )
    | ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k1_tarski @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['25','35'])).

thf('37',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('39',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ X48 @ X49 )
      | ~ ( v1_relat_1 @ X50 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X50 @ X48 ) @ X49 )
        = ( k7_relat_1 @ X50 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','36'])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['25','35'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5qeQLHSGFj
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 297 iterations in 0.111s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.57  thf(t111_relat_1, conjecture,
% 0.37/0.57    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.37/0.57  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t60_relat_1, axiom,
% 0.37/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.57  thf(t98_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X51 : $i]:
% 0.37/0.57         (((k7_relat_1 @ X51 @ (k1_relat_1 @ X51)) = (X51))
% 0.37/0.57          | ~ (v1_relat_1 @ X51))),
% 0.37/0.57      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.57        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf(d1_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) <=>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.57              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X45 : $i]: ((v1_relat_1 @ X45) | (r2_hidden @ (sk_B @ X45) @ X45))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.37/0.57  thf(l1_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X33 : $i, X35 : $i]:
% 0.37/0.57         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.37/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf(t3_xboole_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf(t69_enumset1, axiom,
% 0.37/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.57  thf('10', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.57  thf(t19_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.37/0.57       ( k1_tarski @ A ) ))).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X36 : $i, X37 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))
% 0.37/0.57           = (k1_tarski @ X36))),
% 0.37/0.57      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.37/0.57           = (k1_tarski @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('13', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.57  thf(t12_setfam_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X41 : $i, X42 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.37/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['12', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((((k1_setfam_1 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.57          = (k1_tarski @ (sk_B @ k1_xboole_0)))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['9', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      ((((k1_setfam_1 @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['8', '17'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k1_setfam_1 @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf(t100_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ X0)
% 0.37/0.57           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.57          = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['19', '22'])).
% 0.37/0.57  thf(t92_xboole_1, axiom,
% 0.37/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf('24', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf(t20_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.57         ( k1_tarski @ A ) ) <=>
% 0.37/0.57       ( ( A ) != ( B ) ) ))).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X38 : $i, X39 : $i]:
% 0.37/0.57         (((X39) != (X38))
% 0.37/0.57          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 0.37/0.57              != (k1_tarski @ X39)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X38 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 0.37/0.57           != (k1_tarski @ X38))),
% 0.37/0.57      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      ((((k4_xboole_0 @ (k1_tarski @ (sk_B @ k1_xboole_0)) @ k1_xboole_0)
% 0.37/0.57          != (k1_tarski @ (sk_B @ k1_xboole_0)))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '30'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.57          != (k1_tarski @ (sk_B @ k1_xboole_0)))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.57            != (k1_tarski @ (sk_B @ k1_xboole_0))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.37/0.57        | ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.57  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.57      inference('clc', [status(thm)], ['25', '35'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['3', '36'])).
% 0.37/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.57  thf('38', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.57  thf(t102_relat_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ C ) =>
% 0.37/0.57       ( ( r1_tarski @ A @ B ) =>
% 0.37/0.57         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X48 @ X49)
% 0.37/0.57          | ~ (v1_relat_1 @ X50)
% 0.37/0.57          | ((k7_relat_1 @ (k7_relat_1 @ X50 @ X48) @ X49)
% 0.37/0.57              = (k7_relat_1 @ X50 @ X48)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k7_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 0.37/0.57            = (k7_relat_1 @ X1 @ k1_xboole_0))
% 0.37/0.57          | ~ (v1_relat_1 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 0.37/0.57            = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.37/0.57          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['37', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['3', '36'])).
% 0.37/0.57  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.57      inference('clc', [status(thm)], ['25', '35'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.37/0.57  thf('45', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '44'])).
% 0.37/0.57  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
