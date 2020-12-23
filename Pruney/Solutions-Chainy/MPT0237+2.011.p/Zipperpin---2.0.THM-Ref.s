%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cUI6HGjZLG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 5.50s
% Output     : Refutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 ( 742 expanded)
%              Number of equality atoms :   54 (  92 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X64 ) @ X65 )
      | ( r2_hidden @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X70: $i,X71: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X70 ) @ ( k1_tarski @ X71 ) )
        = ( k2_tarski @ X70 @ X71 ) )
      | ( X70 = X71 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('13',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('14',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','15','36','37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cUI6HGjZLG
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:13:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 5.50/5.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.50/5.77  % Solved by: fo/fo7.sh
% 5.50/5.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.50/5.77  % done 6320 iterations in 5.338s
% 5.50/5.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.50/5.77  % SZS output start Refutation
% 5.50/5.77  thf(sk_B_type, type, sk_B: $i > $i).
% 5.50/5.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.50/5.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.50/5.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.50/5.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.50/5.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.50/5.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.50/5.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.50/5.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.50/5.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.50/5.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.50/5.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.50/5.77  thf(sk_A_type, type, sk_A: $i).
% 5.50/5.77  thf(t32_zfmisc_1, conjecture,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 5.50/5.77       ( k2_tarski @ A @ B ) ))).
% 5.50/5.77  thf(zf_stmt_0, negated_conjecture,
% 5.50/5.77    (~( ![A:$i,B:$i]:
% 5.50/5.77        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 5.50/5.77          ( k2_tarski @ A @ B ) ) )),
% 5.50/5.77    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 5.50/5.77  thf('0', plain,
% 5.50/5.77      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 5.50/5.77         != (k2_tarski @ sk_A @ sk_B_1))),
% 5.50/5.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.77  thf(l51_zfmisc_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.50/5.77  thf('1', plain,
% 5.50/5.77      (![X68 : $i, X69 : $i]:
% 5.50/5.77         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 5.50/5.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.77  thf('2', plain,
% 5.50/5.77      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 5.50/5.77         != (k2_tarski @ sk_A @ sk_B_1))),
% 5.50/5.77      inference('demod', [status(thm)], ['0', '1'])).
% 5.50/5.77  thf(l27_zfmisc_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 5.50/5.77  thf('3', plain,
% 5.50/5.77      (![X64 : $i, X65 : $i]:
% 5.50/5.77         ((r1_xboole_0 @ (k1_tarski @ X64) @ X65) | (r2_hidden @ X64 @ X65))),
% 5.50/5.77      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 5.50/5.77  thf(t83_xboole_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.50/5.77  thf('4', plain,
% 5.50/5.77      (![X14 : $i, X15 : $i]:
% 5.50/5.77         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 5.50/5.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.50/5.77  thf('5', plain,
% 5.50/5.77      (![X0 : $i, X1 : $i]:
% 5.50/5.77         ((r2_hidden @ X1 @ X0)
% 5.50/5.77          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 5.50/5.77      inference('sup-', [status(thm)], ['3', '4'])).
% 5.50/5.77  thf(t98_xboole_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.50/5.77  thf('6', plain,
% 5.50/5.77      (![X17 : $i, X18 : $i]:
% 5.50/5.77         ((k2_xboole_0 @ X17 @ X18)
% 5.50/5.77           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 5.50/5.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.50/5.77  thf('7', plain,
% 5.50/5.77      (![X0 : $i, X1 : $i]:
% 5.50/5.77         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 5.50/5.77            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.50/5.77          | (r2_hidden @ X0 @ X1))),
% 5.50/5.77      inference('sup+', [status(thm)], ['5', '6'])).
% 5.50/5.77  thf(t29_zfmisc_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( ( A ) != ( B ) ) =>
% 5.50/5.77       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 5.50/5.77         ( k2_tarski @ A @ B ) ) ))).
% 5.50/5.77  thf('8', plain,
% 5.50/5.77      (![X70 : $i, X71 : $i]:
% 5.50/5.77         (((k5_xboole_0 @ (k1_tarski @ X70) @ (k1_tarski @ X71))
% 5.50/5.77            = (k2_tarski @ X70 @ X71))
% 5.50/5.77          | ((X70) = (X71)))),
% 5.50/5.77      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 5.50/5.77  thf('9', plain,
% 5.50/5.77      (![X0 : $i, X1 : $i]:
% 5.50/5.77         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 5.50/5.77            = (k2_tarski @ X1 @ X0))
% 5.50/5.77          | (r2_hidden @ X0 @ (k1_tarski @ X1))
% 5.50/5.77          | ((X1) = (X0)))),
% 5.50/5.77      inference('sup+', [status(thm)], ['7', '8'])).
% 5.50/5.77  thf(d1_tarski, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 5.50/5.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 5.50/5.77  thf('10', plain,
% 5.50/5.77      (![X31 : $i, X33 : $i, X34 : $i]:
% 5.50/5.77         (~ (r2_hidden @ X34 @ X33)
% 5.50/5.77          | ((X34) = (X31))
% 5.50/5.77          | ((X33) != (k1_tarski @ X31)))),
% 5.50/5.77      inference('cnf', [status(esa)], [d1_tarski])).
% 5.50/5.77  thf('11', plain,
% 5.50/5.77      (![X31 : $i, X34 : $i]:
% 5.50/5.77         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 5.50/5.77      inference('simplify', [status(thm)], ['10'])).
% 5.50/5.77  thf('12', plain,
% 5.50/5.77      (![X0 : $i, X1 : $i]:
% 5.50/5.77         (((X1) = (X0))
% 5.50/5.77          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 5.50/5.77              = (k2_tarski @ X1 @ X0)))),
% 5.50/5.77      inference('clc', [status(thm)], ['9', '11'])).
% 5.50/5.77  thf('13', plain,
% 5.50/5.77      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 5.50/5.77         != (k2_tarski @ sk_A @ sk_B_1))),
% 5.50/5.77      inference('demod', [status(thm)], ['0', '1'])).
% 5.50/5.77  thf('14', plain,
% 5.50/5.77      ((((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))
% 5.50/5.77        | ((sk_A) = (sk_B_1)))),
% 5.50/5.77      inference('sup-', [status(thm)], ['12', '13'])).
% 5.50/5.77  thf('15', plain, (((sk_A) = (sk_B_1))),
% 5.50/5.77      inference('simplify', [status(thm)], ['14'])).
% 5.50/5.77  thf(idempotence_k3_xboole_0, axiom,
% 5.50/5.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 5.50/5.77  thf('16', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 5.50/5.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 5.50/5.77  thf(t100_xboole_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.50/5.77  thf('17', plain,
% 5.50/5.77      (![X8 : $i, X9 : $i]:
% 5.50/5.77         ((k4_xboole_0 @ X8 @ X9)
% 5.50/5.77           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 5.50/5.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.50/5.77  thf('18', plain,
% 5.50/5.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.50/5.77      inference('sup+', [status(thm)], ['16', '17'])).
% 5.50/5.77  thf(t7_xboole_0, axiom,
% 5.50/5.77    (![A:$i]:
% 5.50/5.77     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.50/5.77          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 5.50/5.77  thf('19', plain,
% 5.50/5.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 5.50/5.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.50/5.77  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 5.50/5.77  thf('20', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 5.50/5.77      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.50/5.77  thf('21', plain,
% 5.50/5.77      (![X14 : $i, X15 : $i]:
% 5.50/5.77         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 5.50/5.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.50/5.77  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.50/5.77      inference('sup-', [status(thm)], ['20', '21'])).
% 5.50/5.77  thf(t48_xboole_1, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.50/5.77  thf('23', plain,
% 5.50/5.77      (![X10 : $i, X11 : $i]:
% 5.50/5.77         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 5.50/5.77           = (k3_xboole_0 @ X10 @ X11))),
% 5.50/5.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.50/5.77  thf('24', plain,
% 5.50/5.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 5.50/5.77      inference('sup+', [status(thm)], ['22', '23'])).
% 5.50/5.77  thf('25', plain,
% 5.50/5.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.50/5.77      inference('sup+', [status(thm)], ['16', '17'])).
% 5.50/5.77  thf('26', plain,
% 5.50/5.77      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 5.50/5.77      inference('demod', [status(thm)], ['24', '25'])).
% 5.50/5.77  thf(t4_xboole_0, axiom,
% 5.50/5.77    (![A:$i,B:$i]:
% 5.50/5.77     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 5.50/5.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.50/5.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.50/5.77            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 5.50/5.77  thf('27', plain,
% 5.50/5.77      (![X3 : $i, X5 : $i, X6 : $i]:
% 5.50/5.77         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 5.50/5.77          | ~ (r1_xboole_0 @ X3 @ X6))),
% 5.50/5.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 5.50/5.77  thf('28', plain,
% 5.50/5.77      (![X0 : $i, X1 : $i]:
% 5.50/5.77         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 5.50/5.77          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 5.50/5.77      inference('sup-', [status(thm)], ['26', '27'])).
% 5.50/5.77  thf('29', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 5.50/5.77      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.50/5.77  thf('30', plain,
% 5.50/5.77      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 5.50/5.77      inference('demod', [status(thm)], ['28', '29'])).
% 5.50/5.77  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.50/5.77      inference('sup-', [status(thm)], ['19', '30'])).
% 5.50/5.77  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.50/5.77      inference('demod', [status(thm)], ['18', '31'])).
% 5.50/5.77  thf('33', plain,
% 5.50/5.77      (![X17 : $i, X18 : $i]:
% 5.50/5.77         ((k2_xboole_0 @ X17 @ X18)
% 5.50/5.77           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 5.50/5.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.50/5.77  thf('34', plain,
% 5.50/5.77      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.50/5.77      inference('sup+', [status(thm)], ['32', '33'])).
% 5.50/5.77  thf(t5_boole, axiom,
% 5.50/5.77    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.50/5.77  thf('35', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 5.50/5.77      inference('cnf', [status(esa)], [t5_boole])).
% 5.50/5.77  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 5.50/5.77      inference('demod', [status(thm)], ['34', '35'])).
% 5.50/5.77  thf('37', plain, (((sk_A) = (sk_B_1))),
% 5.50/5.77      inference('simplify', [status(thm)], ['14'])).
% 5.50/5.77  thf(t69_enumset1, axiom,
% 5.50/5.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.50/5.77  thf('38', plain,
% 5.50/5.77      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 5.50/5.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.50/5.77  thf('39', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 5.50/5.77      inference('demod', [status(thm)], ['2', '15', '36', '37', '38'])).
% 5.50/5.77  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 5.50/5.77  
% 5.50/5.77  % SZS output end Refutation
% 5.50/5.77  
% 5.50/5.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
