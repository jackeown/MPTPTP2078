%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YPQ70E7vgn

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:23 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 181 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  566 (1545 expanded)
%              Number of equality atoms :   46 ( 135 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('36',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['19'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('41',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['20','42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['18','44'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B_1 )
    | ( k1_xboole_0 = sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('52',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('54',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('55',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','42'])).

thf('57',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YPQ70E7vgn
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:41:48 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 210 iterations in 0.097s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(t38_subset_1, conjecture,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.53       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.53         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i,B:$i]:
% 0.37/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.53          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.53            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.37/0.53  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(d5_subset_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.53  thf('1', plain,
% 0.37/0.53      (![X22 : $i, X23 : $i]:
% 0.37/0.53         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.37/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.37/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.53  thf(d3_tarski, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (![X3 : $i, X5 : $i]:
% 0.37/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X3 : $i, X5 : $i]:
% 0.37/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf(d5_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.53       ( ![D:$i]:
% 0.37/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.53  thf('5', plain,
% 0.37/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.53          | (r2_hidden @ X6 @ X8)
% 0.37/0.53          | (r2_hidden @ X6 @ X9)
% 0.37/0.53          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.53  thf('6', plain,
% 0.37/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.53         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.37/0.53          | (r2_hidden @ X6 @ X8)
% 0.37/0.53          | ~ (r2_hidden @ X6 @ X7))),
% 0.37/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((r1_tarski @ X0 @ X1)
% 0.37/0.53          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.37/0.53          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X3 : $i, X5 : $i]:
% 0.37/0.53         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.37/0.53          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.53          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.53          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.53  thf('11', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X10 @ X9)
% 0.37/0.53          | ~ (r2_hidden @ X10 @ X8)
% 0.37/0.53          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.53          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((r1_tarski @ X2 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.53          | ~ (r2_hidden @ 
% 0.37/0.53               (sk_C @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.53          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['3', '13'])).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      ((r1_tarski @ sk_B_1 @ 
% 0.37/0.53        (k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.53      inference('sup+', [status(thm)], ['2', '15'])).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.37/0.53        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.53      inference('split', [status(esa)], ['17'])).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.37/0.53        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('20', plain,
% 0.37/0.53      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.37/0.53       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.53      inference('split', [status(esa)], ['19'])).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      (![X3 : $i, X5 : $i]:
% 0.37/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf(t7_xboole_0, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.53  thf('22', plain,
% 0.37/0.53      (![X12 : $i]:
% 0.37/0.53         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.53  thf('23', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X10 @ X9)
% 0.37/0.53          | (r2_hidden @ X10 @ X7)
% 0.37/0.53          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.53         ((r2_hidden @ X10 @ X7)
% 0.37/0.53          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.53  thf('25', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['22', '24'])).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (![X12 : $i]:
% 0.37/0.53         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.53          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.53  thf('28', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.53          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.53  thf('29', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.37/0.53          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['25', '28'])).
% 0.37/0.53  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.53          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.53  thf('32', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.53  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.53      inference('condensation', [status(thm)], ['32'])).
% 0.37/0.53  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['21', '33'])).
% 0.37/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.53  thf('35', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.53  thf('36', plain,
% 0.37/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.37/0.53         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.53      inference('split', [status(esa)], ['17'])).
% 0.37/0.53  thf('37', plain,
% 0.37/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.53  thf('38', plain,
% 0.37/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.54      inference('split', [status(esa)], ['19'])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.37/0.54         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.37/0.54             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.54  thf('41', plain,
% 0.37/0.54      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.37/0.54         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.37/0.54             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.54       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['34', '41'])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.54       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.54      inference('split', [status(esa)], ['17'])).
% 0.37/0.54  thf('44', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['20', '42', '43'])).
% 0.37/0.54  thf('45', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['18', '44'])).
% 0.37/0.54  thf(l32_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      (![X16 : $i, X18 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X16 @ X18))),
% 0.37/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.54  thf('48', plain, ((r1_tarski @ sk_B_1 @ k1_xboole_0)),
% 0.37/0.54      inference('demod', [status(thm)], ['16', '47'])).
% 0.37/0.54  thf(d10_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      (![X13 : $i, X15 : $i]:
% 0.37/0.54         (((X13) = (X15))
% 0.37/0.54          | ~ (r1_tarski @ X15 @ X13)
% 0.37/0.54          | ~ (r1_tarski @ X13 @ X15))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('50', plain,
% 0.37/0.54      ((~ (r1_tarski @ k1_xboole_0 @ sk_B_1) | ((k1_xboole_0) = (sk_B_1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.54  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '33'])).
% 0.37/0.54  thf('52', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.37/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.54  thf('53', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.37/0.54         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.54      inference('split', [status(esa)], ['19'])).
% 0.37/0.54  thf('55', plain,
% 0.37/0.54      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.54  thf('56', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['20', '42'])).
% 0.37/0.54  thf('57', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['55', '56'])).
% 0.37/0.54  thf('58', plain, ($false),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['52', '57'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
