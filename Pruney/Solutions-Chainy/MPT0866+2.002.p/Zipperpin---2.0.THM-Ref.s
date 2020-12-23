%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2fwo4Pnxpi

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 (  93 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  490 ( 788 expanded)
%              Number of equality atoms :   68 ( 115 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t24_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( C
                  = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_mcart_1])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k1_tarski @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( sk_E @ X17 @ X18 @ X19 ) @ ( sk_F @ X17 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
      | ( X0
        = ( k4_tarski @ ( sk_E @ sk_B_1 @ sk_A @ X0 ) @ ( sk_F @ sk_B_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( sk_E @ sk_B_1 @ sk_A @ sk_C_1 ) @ ( sk_F @ sk_B_1 @ sk_A @ sk_C_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( v1_relat_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k4_tarski @ ( k1_mcart_1 @ X21 ) @ ( k2_mcart_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    sk_C_1
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B @ ( k1_tarski @ sk_C_1 ) )
    = sk_C_1 ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ( ( sk_B @ X14 )
       != ( k4_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
       != ( k4_tarski @ X1 @ X0 ) )
      | ( v1_relat_1 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_relat_1 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,
    ( ( v1_relat_1 @ ( k1_tarski @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X8 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_relat_1 @ ( k1_tarski @ sk_C_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_relat_1 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ ( k1_tarski @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,
    ( sk_C_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C_1
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2fwo4Pnxpi
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 60 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(d2_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((X1) != (X0))
% 0.20/0.49          | (r2_hidden @ X1 @ X2)
% 0.20/0.49          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.49  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.49  thf(t24_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ~( ![C:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.49                 ( ( C ) =
% 0.20/0.49                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ~( ![C:$i]:
% 0.20/0.49                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.49                    ( ( C ) =
% 0.20/0.49                      ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t24_mcart_1])).
% 0.20/0.49  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t55_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.49       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (((X10) = (k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ X11 @ X10)
% 0.20/0.49          | (m1_subset_1 @ (k1_tarski @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.20/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t6_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.49       ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.49            ( ![E:$i,F:$i]:
% 0.20/0.49              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.49                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (((X19)
% 0.20/0.49            = (k4_tarski @ (sk_E @ X17 @ X18 @ X19) @ (sk_F @ X17 @ X18 @ X19)))
% 0.20/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.20/0.49          | ~ (r2_hidden @ X19 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.20/0.49          | ((X0)
% 0.20/0.49              = (k4_tarski @ (sk_E @ sk_B_1 @ sk_A @ X0) @ 
% 0.20/0.49                 (sk_F @ sk_B_1 @ sk_A @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((((sk_C_1)
% 0.20/0.49          = (k4_tarski @ (sk_E @ sk_B_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.49             (sk_F @ sk_B_1 @ sk_A @ sk_C_1)))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.49  thf('10', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(d1_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.49              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X14 : $i]: ((v1_relat_1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ((X4) = (X3))
% 0.20/0.49          | ((X4) = (X0))
% 0.20/0.49          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (((X4) = (X0))
% 0.20/0.49          | ((X4) = (X3))
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k2_tarski @ X1 @ X0))
% 0.20/0.49          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.20/0.49          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k1_tarski @ X0))
% 0.20/0.49          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))
% 0.20/0.49          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['10', '14'])).
% 0.20/0.49  thf('16', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('17', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k1_tarski @ X0))
% 0.20/0.49          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.49          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_B @ (k1_tarski @ X0)) = (X0)) | (v1_relat_1 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.49  thf(t23_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.49         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         (((X21) = (k4_tarski @ (k1_mcart_1 @ X21) @ (k2_mcart_1 @ X21)))
% 0.20/0.49          | ~ (v1_relat_1 @ X22)
% 0.20/0.49          | ~ (r2_hidden @ X21 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_tarski @ X0))
% 0.20/0.49          | ((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.49          | ((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((sk_C_1) != (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((((sk_C_1) != (sk_C_1)) | ((sk_B @ (k1_tarski @ sk_C_1)) = (sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, (((sk_B @ (k1_tarski @ sk_C_1)) = (sk_C_1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X14) | ((sk_B @ X14) != (k4_tarski @ X15 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((sk_C_1) != (k4_tarski @ X1 @ X0))
% 0.20/0.49          | (v1_relat_1 @ (k1_tarski @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_C_1) != (sk_C_1))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.20/0.49        | (v1_relat_1 @ (k1_tarski @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((v1_relat_1 @ (k1_tarski @ sk_C_1))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (((X7) = (k1_xboole_0))
% 0.20/0.49          | ((X8) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X8 @ X7) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | (v1_relat_1 @ (k1_tarski @ sk_C_1))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | (v1_relat_1 @ (k1_tarski @ sk_C_1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.49  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain, ((v1_relat_1 @ (k1_tarski @ sk_C_1))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['33', '34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_tarski @ X0))
% 0.20/0.49          | ((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((sk_C_1) != (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
