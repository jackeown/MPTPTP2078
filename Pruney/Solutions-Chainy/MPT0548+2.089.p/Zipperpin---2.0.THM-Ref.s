%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sDQsBVlUMe

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:13 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 110 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  448 ( 806 expanded)
%              Number of equality atoms :   38 (  77 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('3',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X8 @ ( k1_tarski @ X7 ) )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ k1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) )
        = X8 )
      | ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_tarski @ X2 @ X2 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X8 @ ( k1_tarski @ X7 ) )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('30',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ sk_A ) ) @ ( k9_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ sk_A ) ) @ ( k9_relat_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_A @ ( sk_C @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ sk_A ) ) ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_A @ ( sk_C @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ sk_A ) ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sDQsBVlUMe
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 78 iterations in 0.070s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.34/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(t113_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i]:
% 0.34/0.52         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.34/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.34/0.52  thf(fc6_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.34/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.52  thf('3', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.34/0.52  thf(t2_tarski, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.34/0.52       ( ( A ) = ( B ) ) ))).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((X1) = (X0))
% 0.34/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.34/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.34/0.52  thf(t4_boole, axiom,
% 0.34/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.34/0.52  thf(t65_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.34/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X7 : $i, X8 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X7 @ X8)
% 0.34/0.52          | ((k4_xboole_0 @ X8 @ (k1_tarski @ X7)) != (X8)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.52  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['4', '8'])).
% 0.34/0.52  thf(t143_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ C ) =>
% 0.34/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.34/0.52         ( ?[D:$i]:
% 0.34/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.34/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.34/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.34/0.52          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | (r2_hidden @ 
% 0.34/0.52             (sk_D @ X1 @ X0 @ (sk_C @ k1_xboole_0 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.34/0.52             X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((X1) = (X0))
% 0.34/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.34/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.34/0.52  thf(t69_enumset1, axiom,
% 0.34/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.52  thf('15', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X8 : $i, X9 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X8 @ (k1_tarski @ X9)) = (X8))
% 0.34/0.52          | (r2_hidden @ X9 @ X8))),
% 0.34/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) = (X1))
% 0.34/0.52          | (r2_hidden @ X0 @ X1))),
% 0.34/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.34/0.52          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ (k2_tarski @ X2 @ X2))
% 0.34/0.52            = (k9_relat_1 @ X1 @ X0))
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | (r2_hidden @ (sk_D @ X1 @ X0 @ X2) @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.52  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X1)
% 0.34/0.52          | ((k4_xboole_0 @ (k9_relat_1 @ X1 @ k1_xboole_0) @ 
% 0.34/0.52              (k2_tarski @ X0 @ X0)) = (k9_relat_1 @ X1 @ k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.52  thf('22', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (![X7 : $i, X8 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X7 @ X8)
% 0.34/0.52          | ((k4_xboole_0 @ X8 @ (k1_tarski @ X7)) != (X8)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 0.34/0.52          | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((k9_relat_1 @ X0 @ k1_xboole_0) != (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.34/0.52          | ~ (v1_relat_1 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['21', '24'])).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.34/0.52          | ~ (v1_relat_1 @ X0))),
% 0.34/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ (sk_C @ (k9_relat_1 @ X0 @ k1_xboole_0) @ X1) @ X1)
% 0.34/0.52          | ((X1) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.34/0.52          | ~ (v1_relat_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['14', '26'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | ((X0) = (k9_relat_1 @ X1 @ k1_xboole_0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['13', '27'])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((X0) = (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.34/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.34/0.52  thf(t150_relat_1, conjecture,
% 0.34/0.52    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.34/0.52  thf('30', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.34/0.52          | (r2_hidden @ 
% 0.34/0.52             (sk_C @ k1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ sk_A)) @ 
% 0.34/0.52             (k9_relat_1 @ k1_xboole_0 @ sk_A))
% 0.34/0.52          | ~ (v1_relat_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | (r2_hidden @ 
% 0.34/0.52             (sk_C @ k1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ sk_A)) @ 
% 0.34/0.52             (k9_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.34/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.34/0.52          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k1_relat_1 @ X15))
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.34/0.52          | (r2_hidden @ 
% 0.34/0.52             (sk_D @ k1_xboole_0 @ sk_A @ 
% 0.34/0.52              (sk_C @ k1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ sk_A))) @ 
% 0.34/0.52             (k1_relat_1 @ k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.34/0.52  thf(t60_relat_1, axiom,
% 0.34/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.34/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.52  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | (r2_hidden @ 
% 0.34/0.52             (sk_D @ k1_xboole_0 @ sk_A @ 
% 0.34/0.52              (sk_C @ k1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ sk_A))) @ 
% 0.34/0.52             k1_xboole_0))),
% 0.34/0.52      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.34/0.52  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf('40', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.34/0.52      inference('clc', [status(thm)], ['38', '39'])).
% 0.34/0.52  thf('41', plain, ($false), inference('sup-', [status(thm)], ['3', '40'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
