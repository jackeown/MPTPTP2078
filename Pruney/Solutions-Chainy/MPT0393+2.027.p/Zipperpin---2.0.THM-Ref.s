%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hY9GcAsovh

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:44 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 205 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  399 (1578 expanded)
%              Number of equality atoms :   51 ( 175 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X38 @ X37 ) @ X37 )
      | ( r1_tarski @ X38 @ ( k1_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ( X13 = X12 )
      | ( X13 = X9 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X13 = X9 )
      | ( X13 = X12 )
      | ~ ( r2_hidden @ X13 @ ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k1_tarski @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r1_tarski @ ( k1_setfam_1 @ X40 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( sk_C @ X38 @ X37 ) )
      | ( r1_tarski @ X38 @ ( k1_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('25',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('36',plain,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != sk_A ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hY9GcAsovh
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.82/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.01  % Solved by: fo/fo7.sh
% 0.82/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.01  % done 817 iterations in 0.571s
% 0.82/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.01  % SZS output start Refutation
% 0.82/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.01  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.82/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.01  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.82/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.01  thf(t6_setfam_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.82/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.82/1.01  thf('0', plain,
% 0.82/1.01      (![X37 : $i, X38 : $i]:
% 0.82/1.01         (((X37) = (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ (sk_C @ X38 @ X37) @ X37)
% 0.82/1.01          | (r1_tarski @ X38 @ (k1_setfam_1 @ X37)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.82/1.01  thf(t69_enumset1, axiom,
% 0.82/1.01    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.01  thf('1', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.82/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.01  thf(d2_tarski, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.82/1.01       ( ![D:$i]:
% 0.82/1.01         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.82/1.01  thf('2', plain,
% 0.82/1.01      (![X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X13 @ X11)
% 0.82/1.01          | ((X13) = (X12))
% 0.82/1.01          | ((X13) = (X9))
% 0.82/1.01          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d2_tarski])).
% 0.82/1.01  thf('3', plain,
% 0.82/1.01      (![X9 : $i, X12 : $i, X13 : $i]:
% 0.82/1.01         (((X13) = (X9))
% 0.82/1.01          | ((X13) = (X12))
% 0.82/1.01          | ~ (r2_hidden @ X13 @ (k2_tarski @ X12 @ X9)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['2'])).
% 0.82/1.01  thf('4', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['1', '3'])).
% 0.82/1.01  thf('5', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['4'])).
% 0.82/1.01  thf('6', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.82/1.01          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['0', '5'])).
% 0.82/1.01  thf(d10_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.82/1.01  thf('7', plain,
% 0.82/1.01      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.01  thf('8', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.82/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.82/1.01  thf('9', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.82/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.82/1.01  thf(l1_zfmisc_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.82/1.01  thf('10', plain,
% 0.82/1.01      (![X21 : $i, X22 : $i]:
% 0.82/1.01         ((r2_hidden @ X21 @ X22) | ~ (r1_tarski @ (k1_tarski @ X21) @ X22))),
% 0.82/1.01      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.82/1.01  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf(t8_setfam_1, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.82/1.01       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.82/1.01  thf('12', plain,
% 0.82/1.01      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X39 @ X40)
% 0.82/1.01          | ~ (r1_tarski @ X39 @ X41)
% 0.82/1.01          | (r1_tarski @ (k1_setfam_1 @ X40) @ X41))),
% 0.82/1.01      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.82/1.01  thf('13', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.82/1.01          | ~ (r1_tarski @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['11', '12'])).
% 0.82/1.01  thf('14', plain,
% 0.82/1.01      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.82/1.01      inference('sup-', [status(thm)], ['8', '13'])).
% 0.82/1.01  thf('15', plain,
% 0.82/1.01      (![X6 : $i, X8 : $i]:
% 0.82/1.01         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.82/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.01  thf('16', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.82/1.01  thf('17', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (((sk_C @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.82/1.01          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['6', '16'])).
% 0.82/1.01  thf('18', plain,
% 0.82/1.01      (![X37 : $i, X38 : $i]:
% 0.82/1.01         (((X37) = (k1_xboole_0))
% 0.82/1.01          | ~ (r1_tarski @ X38 @ (sk_C @ X38 @ X37))
% 0.82/1.01          | (r1_tarski @ X38 @ (k1_setfam_1 @ X37)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.82/1.01  thf('19', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X0 @ X0)
% 0.82/1.01          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.82/1.01          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.01  thf('20', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.82/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.82/1.01  thf('21', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.82/1.01          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.82/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.82/1.01  thf('22', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.82/1.01          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.82/1.01      inference('simplify', [status(thm)], ['21'])).
% 0.82/1.01  thf('23', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.82/1.01  thf('24', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.82/1.01      inference('clc', [status(thm)], ['22', '23'])).
% 0.82/1.01  thf(t11_setfam_1, conjecture,
% 0.82/1.01    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.82/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.01    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.82/1.01    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.82/1.01  thf('25', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('26', plain,
% 0.82/1.01      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['24', '25'])).
% 0.82/1.01  thf('27', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.82/1.01      inference('simplify', [status(thm)], ['26'])).
% 0.82/1.01  thf(t6_zfmisc_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.82/1.01       ( ( A ) = ( B ) ) ))).
% 0.82/1.01  thf('28', plain,
% 0.82/1.01      (![X28 : $i, X29 : $i]:
% 0.82/1.01         (((X29) = (X28))
% 0.82/1.01          | ~ (r1_tarski @ (k1_tarski @ X29) @ (k1_tarski @ X28)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.82/1.01  thf('29', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['27', '28'])).
% 0.82/1.01  thf(t4_subset_1, axiom,
% 0.82/1.01    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.82/1.01  thf('30', plain,
% 0.82/1.01      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.82/1.01      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.82/1.01  thf(t3_subset, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.82/1.01  thf('31', plain,
% 0.82/1.01      (![X31 : $i, X32 : $i]:
% 0.82/1.01         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.82/1.01  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.82/1.01      inference('sup-', [status(thm)], ['30', '31'])).
% 0.82/1.01  thf('33', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['29', '32'])).
% 0.82/1.01  thf('34', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('35', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.82/1.01      inference('simplify', [status(thm)], ['26'])).
% 0.82/1.01  thf('36', plain, (((k1_setfam_1 @ k1_xboole_0) != (sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['34', '35'])).
% 0.82/1.01  thf('37', plain, (((k1_setfam_1 @ k1_xboole_0) != (sk_A))),
% 0.82/1.01      inference('sup-', [status(thm)], ['33', '36'])).
% 0.82/1.01  thf('38', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['29', '32'])).
% 0.82/1.01  thf('39', plain, ($false),
% 0.82/1.01      inference('simplify_reflect+', [status(thm)], ['37', '38'])).
% 0.82/1.01  
% 0.82/1.01  % SZS output end Refutation
% 0.82/1.01  
% 0.82/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
