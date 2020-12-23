%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZILy8mmHMA

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:04 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 123 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   22
%              Number of atoms          :  439 ( 947 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ sk_C_1 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ sk_C_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(condensation,[status(thm)],['29'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_1 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','37'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZILy8mmHMA
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:52:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 159 iterations in 0.095s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(t50_zfmisc_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.54        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf(d3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.54       ( ![D:$i]:
% 0.37/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.54           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X7 : $i, X9 : $i, X11 : $i]:
% 0.37/0.54         (((X11) = (k2_xboole_0 @ X9 @ X7))
% 0.37/0.54          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 0.37/0.54          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 0.37/0.54          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.54  thf(d3_tarski, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X3 : $i, X5 : $i]:
% 0.37/0.54         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X3 : $i, X5 : $i]:
% 0.37/0.54         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.54          | (r2_hidden @ X6 @ X8)
% 0.37/0.54          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.37/0.54         ((r2_hidden @ X6 @ (k2_xboole_0 @ X9 @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.37/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((r1_tarski @ X0 @ X1)
% 0.37/0.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X3 : $i, X5 : $i]:
% 0.37/0.54         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.37/0.54          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['6', '13'])).
% 0.37/0.54  thf('15', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['5', '14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.54          | (r2_hidden @ X2 @ X4)
% 0.37/0.54          | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r1_tarski @ sk_C_1 @ X0)
% 0.37/0.54          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['4', '17'])).
% 0.37/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.54  thf('19', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.54          | (r2_hidden @ X2 @ X4)
% 0.37/0.54          | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X3 : $i, X5 : $i]:
% 0.37/0.54         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | (r1_tarski @ sk_C_1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.54  thf('25', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.37/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.54          | (r2_hidden @ X2 @ X4)
% 0.37/0.54          | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_C_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D @ X1 @ sk_C_1 @ X0) @ X1)
% 0.37/0.54          | (r2_hidden @ (sk_D @ X1 @ sk_C_1 @ X0) @ X0)
% 0.37/0.54          | ((X1) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.37/0.54          | (r2_hidden @ (sk_D @ X1 @ sk_C_1 @ X0) @ X2))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '27'])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D @ X0 @ sk_C_1 @ X0) @ X1)
% 0.37/0.54          | ((X0) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.37/0.54          | (r2_hidden @ (sk_D @ X0 @ sk_C_1 @ X0) @ X0))),
% 0.37/0.54      inference('eq_fact', [status(thm)], ['28'])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D @ X0 @ sk_C_1 @ X0) @ X0)
% 0.37/0.54          | ((X0) = (k2_xboole_0 @ X0 @ sk_C_1)))),
% 0.37/0.54      inference('condensation', [status(thm)], ['29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X7 : $i, X9 : $i, X11 : $i]:
% 0.37/0.54         (((X11) = (k2_xboole_0 @ X9 @ X7))
% 0.37/0.54          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 0.37/0.54          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((X0) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.37/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ sk_C_1 @ X0) @ X0)
% 0.37/0.54          | ((X0) = (k2_xboole_0 @ X0 @ sk_C_1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r2_hidden @ (sk_D @ X0 @ sk_C_1 @ X0) @ X0)
% 0.37/0.54          | ((X0) = (k2_xboole_0 @ X0 @ sk_C_1)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_D @ X0 @ sk_C_1 @ X0) @ X0)
% 0.37/0.54          | ((X0) = (k2_xboole_0 @ X0 @ sk_C_1)))),
% 0.37/0.54      inference('condensation', [status(thm)], ['29'])).
% 0.37/0.54  thf('35', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ sk_C_1))),
% 0.37/0.54      inference('clc', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_C_1 @ X0) = (X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.54  thf('38', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['2', '37'])).
% 0.37/0.54  thf(t41_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k2_tarski @ A @ B ) =
% 0.37/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i]:
% 0.37/0.54         ((k2_tarski @ X13 @ X14)
% 0.37/0.54           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf(t49_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('41', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.54  thf('44', plain, ($false),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['38', '43'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
