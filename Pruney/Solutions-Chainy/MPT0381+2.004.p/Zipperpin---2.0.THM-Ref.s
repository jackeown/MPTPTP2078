%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x19x4HAKBe

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  275 ( 317 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( m1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X30 @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X34 @ X33 )
      | ( m1_subset_1 @ ( k1_tarski @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['1','10'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X8 ) )
      | ( r2_hidden @ X5 @ X8 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X28 )
      | ~ ( r2_hidden @ X26 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ~ ( r2_hidden @ X28 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x19x4HAKBe
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 81 iterations in 0.035s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X13 @ X14)
% 0.21/0.49           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf(t63_subset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.21/0.49  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d2_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X30 : $i, X31 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X30 @ X31)
% 0.21/0.49          | (m1_subset_1 @ X30 @ X31)
% 0.21/0.49          | (v1_xboole_0 @ X31))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X30 : $i, X31 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X30 @ X31) | ~ (r2_hidden @ X30 @ X31))),
% 0.21/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((m1_subset_1 @ sk_A @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf(t55_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.49       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X33 : $i, X34 : $i]:
% 0.21/0.49         (((X33) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X34 @ X33)
% 0.21/0.49          | (m1_subset_1 @ (k1_tarski @ X34) @ (k1_zfmisc_1 @ X33)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.49        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '10'])).
% 0.21/0.49  thf(t1_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.49       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.49         ((r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X8))
% 0.21/0.49          | (r2_hidden @ X5 @ X8)
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_A @ X0)
% 0.21/0.49          | (r2_hidden @ sk_A @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_A @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.49          | (r2_hidden @ sk_A @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_A @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.49          | ~ (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.49  thf('18', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf(t4_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.21/0.49          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['17', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]: (r2_hidden @ sk_A @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '23'])).
% 0.21/0.49  thf(t64_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.49         (((X26) != (X28))
% 0.21/0.49          | ~ (r2_hidden @ X26 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X27 : $i, X28 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X28 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.49  thf('27', plain, ($false), inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
