%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6an7UN3NAG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:27 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 108 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  510 ( 835 expanded)
%              Number of equality atoms :   41 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
      | ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X14: $i] :
      ( ( r1_xboole_0 @ X14 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','44'])).

thf('46',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['47'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','52'])).

thf('54',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6an7UN3NAG
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 1637 iterations in 0.896s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.15/1.35  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.15/1.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.15/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.35  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.15/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.35  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.35  thf(t149_zfmisc_1, conjecture,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.15/1.35         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.15/1.35       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.15/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.35    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.15/1.35            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.15/1.35          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.15/1.35  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(d7_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.15/1.35       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['1', '2'])).
% 1.15/1.35  thf(commutativity_k3_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['3', '4'])).
% 1.15/1.35  thf(l27_zfmisc_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.15/1.35  thf('6', plain,
% 1.15/1.35      (![X40 : $i, X41 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ (k1_tarski @ X40) @ X41) | (r2_hidden @ X40 @ X41))),
% 1.15/1.35      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.15/1.35  thf('7', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('8', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ X1 @ X0)
% 1.15/1.35          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.35  thf('9', plain,
% 1.15/1.35      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('10', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.15/1.35      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.35  thf(t28_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.15/1.35  thf('12', plain,
% 1.15/1.35      (![X12 : $i, X13 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.15/1.35      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.35  thf('13', plain,
% 1.15/1.35      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.15/1.35         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['11', '12'])).
% 1.15/1.35  thf('14', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('15', plain,
% 1.15/1.35      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.15/1.35         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['13', '14'])).
% 1.15/1.35  thf('16', plain,
% 1.15/1.35      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 1.15/1.35        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['8', '15'])).
% 1.15/1.35  thf('17', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('18', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['3', '4'])).
% 1.15/1.35  thf(t16_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.15/1.35       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.15/1.35  thf('19', plain,
% 1.15/1.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.15/1.35           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.15/1.35  thf('20', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('21', plain,
% 1.15/1.35      (![X2 : $i, X4 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('22', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['20', '21'])).
% 1.15/1.35  thf('23', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.15/1.35          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['19', '22'])).
% 1.15/1.35  thf('24', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 1.15/1.35          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['18', '23'])).
% 1.15/1.35  thf(t66_xboole_1, axiom,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.15/1.35       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.15/1.35  thf('25', plain,
% 1.15/1.35      (![X14 : $i]: ((r1_xboole_0 @ X14 @ X14) | ((X14) != (k1_xboole_0)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.15/1.35  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.15/1.35      inference('simplify', [status(thm)], ['25'])).
% 1.15/1.35  thf(t3_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.15/1.35            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.15/1.35       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.15/1.35            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.15/1.35  thf('27', plain,
% 1.15/1.35      (![X5 : $i, X6 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 1.15/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.15/1.35  thf('28', plain,
% 1.15/1.35      (![X5 : $i, X6 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 1.15/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.15/1.35  thf('29', plain,
% 1.15/1.35      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X7 @ X5)
% 1.15/1.35          | ~ (r2_hidden @ X7 @ X8)
% 1.15/1.35          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.15/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.15/1.35  thf('30', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X0 @ X1)
% 1.15/1.35          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.15/1.35          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.15/1.35      inference('sup-', [status(thm)], ['28', '29'])).
% 1.15/1.35  thf('31', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X0 @ X1)
% 1.15/1.35          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.15/1.35          | (r1_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['27', '30'])).
% 1.15/1.35  thf('32', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('simplify', [status(thm)], ['31'])).
% 1.15/1.35  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.15/1.35      inference('sup-', [status(thm)], ['26', '32'])).
% 1.15/1.35  thf('34', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('35', plain,
% 1.15/1.35      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['33', '34'])).
% 1.15/1.35  thf('36', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('37', plain,
% 1.15/1.35      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['35', '36'])).
% 1.15/1.35  thf('38', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.35          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.15/1.35      inference('demod', [status(thm)], ['24', '37'])).
% 1.15/1.35  thf('39', plain,
% 1.15/1.35      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.15/1.35      inference('simplify', [status(thm)], ['38'])).
% 1.15/1.35  thf('40', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('41', plain,
% 1.15/1.35      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X7 @ X5)
% 1.15/1.35          | ~ (r2_hidden @ X7 @ X8)
% 1.15/1.35          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.15/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.15/1.35  thf('42', plain,
% 1.15/1.35      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['40', '41'])).
% 1.15/1.35  thf('43', plain,
% 1.15/1.35      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['39', '42'])).
% 1.15/1.35  thf('44', plain,
% 1.15/1.35      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['17', '43'])).
% 1.15/1.35  thf('45', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['16', '44'])).
% 1.15/1.35  thf('46', plain,
% 1.15/1.35      (![X2 : $i, X4 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('47', plain,
% 1.15/1.35      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['45', '46'])).
% 1.15/1.35  thf('48', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.15/1.35      inference('simplify', [status(thm)], ['47'])).
% 1.15/1.35  thf(t78_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( r1_xboole_0 @ A @ B ) =>
% 1.15/1.35       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.15/1.35         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.15/1.35  thf('49', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.15/1.35         (~ (r1_xboole_0 @ X16 @ X17)
% 1.15/1.35          | ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.15/1.35              = (k3_xboole_0 @ X16 @ X18)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.15/1.35  thf('50', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.15/1.35           = (k3_xboole_0 @ sk_B @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['48', '49'])).
% 1.15/1.35  thf('51', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['20', '21'])).
% 1.15/1.35  thf('52', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.15/1.35          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['50', '51'])).
% 1.15/1.35  thf('53', plain,
% 1.15/1.35      ((((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.35        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['5', '52'])).
% 1.15/1.35  thf('54', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.15/1.35      inference('simplify', [status(thm)], ['53'])).
% 1.15/1.35  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 1.15/1.35  
% 1.15/1.35  % SZS output end Refutation
% 1.15/1.35  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
