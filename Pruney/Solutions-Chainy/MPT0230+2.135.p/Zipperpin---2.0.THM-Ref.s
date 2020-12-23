%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n2Y9RRxbcy

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 (  97 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  454 ( 621 expanded)
%              Number of equality atoms :   58 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('6',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','24','27'])).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['6','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X25 )
      | ( X27 = X26 )
      | ( X27 = X23 )
      | ( X25
       != ( k2_tarski @ X26 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('42',plain,(
    ! [X23: $i,X26: $i,X27: $i] :
      ( ( X27 = X23 )
      | ( X27 = X26 )
      | ~ ( r2_hidden @ X27 @ ( k2_tarski @ X26 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    sk_A != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n2Y9RRxbcy
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 69 iterations in 0.039s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(t25_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.50          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.50             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t28_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_2))
% 0.20/0.50         = (k1_tarski @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X12 @ X13)
% 0.20/0.50           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_2))
% 0.20/0.50         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf(l35_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( r2_hidden @ A @ B ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X39 : $i, X40 : $i]:
% 0.20/0.50         ((r2_hidden @ X39 @ X40)
% 0.20/0.50          | ((k4_xboole_0 @ (k1_tarski @ X39) @ X40) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.20/0.50          != (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf(t2_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf(t4_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.20/0.50          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.50  thf('11', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.50  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.50  thf(d7_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X12 @ X13)
% 0.20/0.50           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.50           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X12 @ X13)
% 0.20/0.50           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf(t5_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('21', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf(t98_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X21 @ X22)
% 0.20/0.50           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('26', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['17', '24', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X21 @ X22)
% 0.20/0.50           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf(t46_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.50  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('35', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X12 @ X13)
% 0.20/0.50           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '38'])).
% 0.20/0.50  thf('40', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))),
% 0.20/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.50  thf(d2_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X23 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X27 @ X25)
% 0.20/0.50          | ((X27) = (X26))
% 0.20/0.50          | ((X27) = (X23))
% 0.20/0.50          | ((X25) != (k2_tarski @ X26 @ X23)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X23 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (((X27) = (X23))
% 0.20/0.50          | ((X27) = (X26))
% 0.20/0.50          | ~ (r2_hidden @ X27 @ (k2_tarski @ X26 @ X23)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  thf('43', plain, ((((sk_A) = (sk_B)) | ((sk_A) = (sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.50  thf('44', plain, (((sk_A) != (sk_C_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['43', '44', '45'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
