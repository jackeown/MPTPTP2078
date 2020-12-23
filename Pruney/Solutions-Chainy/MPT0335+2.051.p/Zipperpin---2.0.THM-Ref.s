%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r665CHs2VP

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:19 EST 2020

% Result     : Theorem 7.12s
% Output     : Refutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 191 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  642 (2300 expanded)
%              Number of equality atoms :   57 ( 192 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X21 @ X23 ) @ X22 )
        = ( k2_tarski @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D_1 @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) @ sk_A )
    = ( k2_tarski @ sk_D_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('21',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('46',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('48',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r665CHs2VP
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.12/7.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.12/7.38  % Solved by: fo/fo7.sh
% 7.12/7.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.12/7.38  % done 2535 iterations in 6.929s
% 7.12/7.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.12/7.38  % SZS output start Refutation
% 7.12/7.38  thf(sk_B_type, type, sk_B: $i).
% 7.12/7.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.12/7.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.12/7.38  thf(sk_A_type, type, sk_A: $i).
% 7.12/7.38  thf(sk_D_1_type, type, sk_D_1: $i).
% 7.12/7.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.12/7.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.12/7.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.12/7.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.12/7.38  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.12/7.38  thf(t148_zfmisc_1, conjecture,
% 7.12/7.38    (![A:$i,B:$i,C:$i,D:$i]:
% 7.12/7.38     ( ( ( r1_tarski @ A @ B ) & 
% 7.12/7.38         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 7.12/7.38         ( r2_hidden @ D @ A ) ) =>
% 7.12/7.38       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 7.12/7.38  thf(zf_stmt_0, negated_conjecture,
% 7.12/7.38    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 7.12/7.38        ( ( ( r1_tarski @ A @ B ) & 
% 7.12/7.38            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 7.12/7.38            ( r2_hidden @ D @ A ) ) =>
% 7.12/7.38          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 7.12/7.38    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 7.12/7.38  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 7.12/7.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.12/7.38  thf('1', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 7.12/7.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.12/7.38  thf(t53_zfmisc_1, axiom,
% 7.12/7.38    (![A:$i,B:$i,C:$i]:
% 7.12/7.38     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 7.12/7.38       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 7.12/7.38  thf('2', plain,
% 7.12/7.38      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.12/7.38         (~ (r2_hidden @ X21 @ X22)
% 7.12/7.38          | ~ (r2_hidden @ X23 @ X22)
% 7.12/7.38          | ((k3_xboole_0 @ (k2_tarski @ X21 @ X23) @ X22)
% 7.12/7.38              = (k2_tarski @ X21 @ X23)))),
% 7.12/7.38      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 7.12/7.38  thf('3', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         (((k3_xboole_0 @ (k2_tarski @ sk_D_1 @ X0) @ sk_A)
% 7.12/7.38            = (k2_tarski @ sk_D_1 @ X0))
% 7.12/7.38          | ~ (r2_hidden @ X0 @ sk_A))),
% 7.12/7.38      inference('sup-', [status(thm)], ['1', '2'])).
% 7.12/7.38  thf('4', plain,
% 7.12/7.38      (((k3_xboole_0 @ (k2_tarski @ sk_D_1 @ sk_D_1) @ sk_A)
% 7.12/7.38         = (k2_tarski @ sk_D_1 @ sk_D_1))),
% 7.12/7.38      inference('sup-', [status(thm)], ['0', '3'])).
% 7.12/7.38  thf(t69_enumset1, axiom,
% 7.12/7.38    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.12/7.38  thf('5', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 7.12/7.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.12/7.38  thf('6', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 7.12/7.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.12/7.38  thf('7', plain,
% 7.12/7.38      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 7.12/7.38      inference('demod', [status(thm)], ['4', '5', '6'])).
% 7.12/7.38  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 7.12/7.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.12/7.38  thf(t16_xboole_1, axiom,
% 7.12/7.38    (![A:$i,B:$i,C:$i]:
% 7.12/7.38     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 7.12/7.38       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.12/7.38  thf('9', plain,
% 7.12/7.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 7.12/7.38           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 7.12/7.38      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.12/7.38  thf('10', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)
% 7.12/7.38           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['8', '9'])).
% 7.12/7.38  thf(d4_xboole_0, axiom,
% 7.12/7.38    (![A:$i,B:$i,C:$i]:
% 7.12/7.38     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 7.12/7.38       ( ![D:$i]:
% 7.12/7.38         ( ( r2_hidden @ D @ C ) <=>
% 7.12/7.38           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 7.12/7.38  thf('11', plain,
% 7.12/7.38      (![X5 : $i, X6 : $i, X9 : $i]:
% 7.12/7.38         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 7.12/7.38          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 7.12/7.38          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 7.12/7.38      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.12/7.38  thf('12', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 7.12/7.38      inference('eq_fact', [status(thm)], ['11'])).
% 7.12/7.38  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 7.12/7.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.12/7.38  thf(d3_tarski, axiom,
% 7.12/7.38    (![A:$i,B:$i]:
% 7.12/7.38     ( ( r1_tarski @ A @ B ) <=>
% 7.12/7.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.12/7.38  thf('14', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.12/7.38         (~ (r2_hidden @ X0 @ X1)
% 7.12/7.38          | (r2_hidden @ X0 @ X2)
% 7.12/7.38          | ~ (r1_tarski @ X1 @ X2))),
% 7.12/7.38      inference('cnf', [status(esa)], [d3_tarski])).
% 7.12/7.38  thf('15', plain,
% 7.12/7.38      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 7.12/7.38      inference('sup-', [status(thm)], ['13', '14'])).
% 7.12/7.38  thf('16', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         (((sk_A) = (k3_xboole_0 @ sk_A @ X0))
% 7.12/7.38          | (r2_hidden @ (sk_D @ sk_A @ X0 @ sk_A) @ sk_B))),
% 7.12/7.38      inference('sup-', [status(thm)], ['12', '15'])).
% 7.12/7.38  thf('17', plain,
% 7.12/7.38      (![X5 : $i, X6 : $i, X9 : $i]:
% 7.12/7.38         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 7.12/7.38      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.12/7.38  thf('18', plain,
% 7.12/7.38      ((((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))
% 7.12/7.38        | ~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 7.12/7.38        | ~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 7.12/7.38        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 7.12/7.38      inference('sup-', [status(thm)], ['16', '17'])).
% 7.12/7.38  thf('19', plain,
% 7.12/7.38      ((~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 7.12/7.38        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 7.12/7.38      inference('simplify', [status(thm)], ['18'])).
% 7.12/7.38  thf('20', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 7.12/7.38      inference('eq_fact', [status(thm)], ['11'])).
% 7.12/7.38  thf('21', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 7.12/7.38      inference('clc', [status(thm)], ['19', '20'])).
% 7.12/7.38  thf('22', plain,
% 7.12/7.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 7.12/7.38           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 7.12/7.38      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.12/7.38  thf('23', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ sk_A @ X0)
% 7.12/7.38           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['21', '22'])).
% 7.12/7.38  thf('24', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0))
% 7.12/7.38           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['10', '23'])).
% 7.12/7.38  thf('25', plain,
% 7.12/7.38      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 7.12/7.38         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['7', '24'])).
% 7.12/7.38  thf('26', plain,
% 7.12/7.38      (![X5 : $i, X6 : $i, X9 : $i]:
% 7.12/7.38         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 7.12/7.38          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 7.12/7.38          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 7.12/7.38      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.12/7.38  thf('27', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('eq_fact', [status(thm)], ['26'])).
% 7.12/7.38  thf('28', plain,
% 7.12/7.38      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 7.12/7.38         (~ (r2_hidden @ X8 @ X7)
% 7.12/7.38          | (r2_hidden @ X8 @ X6)
% 7.12/7.38          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 7.12/7.38      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.12/7.38  thf('29', plain,
% 7.12/7.38      (![X5 : $i, X6 : $i, X8 : $i]:
% 7.12/7.38         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.12/7.38      inference('simplify', [status(thm)], ['28'])).
% 7.12/7.38  thf('30', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.12/7.38         (((k3_xboole_0 @ X1 @ X0)
% 7.12/7.38            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 7.12/7.38          | (r2_hidden @ 
% 7.12/7.38             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 7.12/7.38             X0))),
% 7.12/7.38      inference('sup-', [status(thm)], ['27', '29'])).
% 7.12/7.38  thf('31', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('eq_fact', [status(thm)], ['26'])).
% 7.12/7.38  thf('32', plain,
% 7.12/7.38      (![X5 : $i, X6 : $i, X9 : $i]:
% 7.12/7.38         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 7.12/7.38      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.12/7.38  thf('33', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('sup-', [status(thm)], ['31', '32'])).
% 7.12/7.38  thf('34', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('simplify', [status(thm)], ['33'])).
% 7.12/7.38  thf('35', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.12/7.38          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('eq_fact', [status(thm)], ['26'])).
% 7.12/7.38  thf('36', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 7.12/7.38          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 7.12/7.38      inference('clc', [status(thm)], ['34', '35'])).
% 7.12/7.38  thf('37', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         (((k3_xboole_0 @ X1 @ X0)
% 7.12/7.38            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 7.12/7.38          | ((k3_xboole_0 @ X1 @ X0)
% 7.12/7.38              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 7.12/7.38      inference('sup-', [status(thm)], ['30', '36'])).
% 7.12/7.38  thf('38', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ X1 @ X0)
% 7.12/7.38           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('simplify', [status(thm)], ['37'])).
% 7.12/7.38  thf('39', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 7.12/7.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.12/7.38  thf('40', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ sk_A @ X0)
% 7.12/7.38           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['21', '22'])).
% 7.12/7.38  thf('41', plain,
% 7.12/7.38      (((k3_xboole_0 @ sk_A @ sk_C_1)
% 7.12/7.38         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['39', '40'])).
% 7.12/7.38  thf('42', plain,
% 7.12/7.38      (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 7.12/7.38      inference('demod', [status(thm)], ['25', '38', '41'])).
% 7.12/7.38  thf('43', plain,
% 7.12/7.38      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 7.12/7.38      inference('demod', [status(thm)], ['4', '5', '6'])).
% 7.12/7.38  thf('44', plain,
% 7.12/7.38      (![X0 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0))
% 7.12/7.38           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['10', '23'])).
% 7.12/7.38  thf('45', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ X1 @ X0)
% 7.12/7.38           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('simplify', [status(thm)], ['37'])).
% 7.12/7.38  thf('46', plain,
% 7.12/7.38      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A)
% 7.12/7.38         = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 7.12/7.38      inference('sup+', [status(thm)], ['44', '45'])).
% 7.12/7.38  thf('47', plain,
% 7.12/7.38      (![X0 : $i, X1 : $i]:
% 7.12/7.38         ((k3_xboole_0 @ X1 @ X0)
% 7.12/7.38           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.12/7.38      inference('simplify', [status(thm)], ['37'])).
% 7.12/7.38  thf('48', plain,
% 7.12/7.38      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A)
% 7.12/7.38         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 7.12/7.38      inference('demod', [status(thm)], ['46', '47'])).
% 7.12/7.38  thf('49', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 7.12/7.38      inference('sup+', [status(thm)], ['43', '48'])).
% 7.12/7.38  thf('50', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 7.12/7.38      inference('demod', [status(thm)], ['42', '49'])).
% 7.12/7.38  thf('51', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 7.12/7.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.12/7.38  thf('52', plain, ($false),
% 7.12/7.38      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 7.12/7.38  
% 7.12/7.38  % SZS output end Refutation
% 7.12/7.38  
% 7.21/7.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
