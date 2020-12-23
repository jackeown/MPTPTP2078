%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rgOwzC5otr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  451 (1029 expanded)
%              Number of equality atoms :   46 (  99 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X39 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('36',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['24','42'])).

thf('44',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rgOwzC5otr
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 969 iterations in 0.492s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(t148_zfmisc_1, conjecture,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( r1_tarski @ A @ B ) & 
% 0.75/0.94         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.75/0.94         ( r2_hidden @ D @ A ) ) =>
% 0.75/0.94       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94        ( ( ( r1_tarski @ A @ B ) & 
% 0.75/0.94            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.75/0.94            ( r2_hidden @ D @ A ) ) =>
% 0.75/0.94          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.75/0.94  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(l1_zfmisc_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      (![X39 : $i, X41 : $i]:
% 0.75/0.94         ((r1_tarski @ (k1_tarski @ X39) @ X41) | ~ (r2_hidden @ X39 @ X41))),
% 0.75/0.94      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.75/0.94  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.94  thf(l32_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X12 : $i, X14 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.75/0.94          | ~ (r1_tarski @ X12 @ X14))),
% 0.75/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.94  thf(t48_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('5', plain,
% 0.75/0.94      (![X22 : $i, X23 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.75/0.94           = (k3_xboole_0 @ X22 @ X23))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ k1_xboole_0)
% 0.75/0.94         = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ k1_xboole_0)
% 0.75/0.94         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf(t3_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.75/0.94            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.94       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.94            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.94  thf('10', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.94  thf(d5_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.94       ( ![D:$i]:
% 0.75/0.94         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.94           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.94          | ~ (r2_hidden @ X6 @ X4)
% 0.75/0.94          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X4)
% 0.75/0.94          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['10', '12'])).
% 0.75/0.94  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X12 : $i, X14 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.75/0.94          | ~ (r1_tarski @ X12 @ X14))),
% 0.75/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.94  thf('16', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['14', '15'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.94          | (r2_hidden @ X6 @ X3)
% 0.75/0.94          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.94         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['17'])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | (r2_hidden @ X0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['16', '18'])).
% 0.75/0.94  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.94      inference('clc', [status(thm)], ['13', '19'])).
% 0.75/0.94  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['9', '20'])).
% 0.75/0.94  thf(t83_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.94  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['8', '23'])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t16_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.94       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 0.75/0.94           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)
% 0.75/0.94           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['26', '27'])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)
% 0.75/0.94           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['25', '28'])).
% 0.75/0.94  thf('30', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['14', '15'])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X22 : $i, X23 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.75/0.94           = (k3_xboole_0 @ X22 @ X23))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.94  thf('36', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['34', '35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 0.75/0.94           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ sk_A @ X0)
% 0.75/0.94           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_A @ sk_C_1)
% 0.75/0.94         = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['29', '38'])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_C_1 @ sk_A)
% 0.75/0.94         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.75/0.94  thf('43', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_tarski @ sk_D_1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['24', '42'])).
% 0.75/0.94  thf('44', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('46', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 0.75/0.94      inference('demod', [status(thm)], ['44', '45'])).
% 0.75/0.94  thf('47', plain, ($false),
% 0.75/0.94      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
