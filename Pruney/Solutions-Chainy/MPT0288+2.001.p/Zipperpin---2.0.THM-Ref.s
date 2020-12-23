%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mYAfX5kYAa

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 136 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   19
%              Number of atoms          :  421 ( 921 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t95_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','23'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ ( sk_C @ X32 @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ ( k3_tarski @ X28 ) )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( sk_C @ X32 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mYAfX5kYAa
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 347 iterations in 0.096s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(t95_zfmisc_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.56       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i]:
% 0.22/0.56        ( ( r1_tarski @ A @ B ) =>
% 0.22/0.56          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t95_zfmisc_1])).
% 0.22/0.56  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(commutativity_k2_tarski, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (![X25 : $i, X26 : $i]:
% 0.22/0.56         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 0.22/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.56  thf(l51_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X29 : $i, X30 : $i]:
% 0.22/0.56         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.22/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (![X29 : $i, X30 : $i]:
% 0.22/0.56         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.22/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(t3_boole, axiom,
% 0.22/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.56  thf('7', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.22/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.56  thf(d10_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.56  thf('9', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.22/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.56  thf(t43_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.22/0.56       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.56         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.22/0.56          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.22/0.56      inference('sup+', [status(thm)], ['7', '11'])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X8 : $i, X10 : $i]:
% 0.22/0.56         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.22/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.22/0.56          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.22/0.56          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['6', '14'])).
% 0.22/0.56  thf('16', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.22/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.56  thf(t11_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.56         ((r1_tarski @ X13 @ X14)
% 0.22/0.56          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf('19', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.56      inference('demod', [status(thm)], ['15', '18'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf('21', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.56         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.22/0.56          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X1 @ X0)
% 0.22/0.56          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.56  thf('24', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.22/0.56      inference('sup-', [status(thm)], ['1', '23'])).
% 0.22/0.56  thf(t3_xboole_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (![X19 : $i]:
% 0.22/0.56         (((X19) = (k1_xboole_0)) | ~ (r1_tarski @ X19 @ k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.56  thf('26', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.56  thf(t48_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (![X23 : $i, X24 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.22/0.56           = (k3_xboole_0 @ X23 @ X24))),
% 0.22/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.56  thf('29', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.22/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.56  thf('30', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.56  thf(t94_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.22/0.56       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (![X31 : $i, X32 : $i]:
% 0.22/0.56         ((r1_tarski @ (k3_tarski @ X31) @ X32)
% 0.22/0.56          | (r2_hidden @ (sk_C @ X32 @ X31) @ X31))),
% 0.22/0.56      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.22/0.56  thf(d4_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.22/0.56       ( ![D:$i]:
% 0.22/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X6 @ X5)
% 0.22/0.56          | (r2_hidden @ X6 @ X4)
% 0.22/0.56          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.22/0.56         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.22/0.56          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['31', '33'])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.22/0.56          | (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['30', '34'])).
% 0.22/0.56  thf('36', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.22/0.56          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 0.22/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.56  thf(l49_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (![X27 : $i, X28 : $i]:
% 0.22/0.56         ((r1_tarski @ X27 @ (k3_tarski @ X28)) | ~ (r2_hidden @ X27 @ X28))),
% 0.22/0.56      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.22/0.56          | (r1_tarski @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X31 : $i, X32 : $i]:
% 0.22/0.56         ((r1_tarski @ (k3_tarski @ X31) @ X32)
% 0.22/0.56          | ~ (r1_tarski @ (sk_C @ X32 @ X31) @ X32))),
% 0.22/0.56      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 0.22/0.56        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.56  thf('42', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.22/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.56  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
