%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8GRZ0VGTif

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:38 EST 2020

% Result     : Theorem 5.08s
% Output     : Refutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 129 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  432 (1413 expanded)
%              Number of equality atoms :   26 (  78 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_C_1 )
      | ( r2_hidden @ X11 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_B_1 = sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ( sk_B_1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A )
      | ( sk_B_1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( sk_B_1 = X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_A )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_B_1 )
      | ( r2_hidden @ X11 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('33',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('37',plain,(
    sk_B_1 = sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8GRZ0VGTif
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:26:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 5.08/5.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.08/5.35  % Solved by: fo/fo7.sh
% 5.08/5.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.08/5.35  % done 1653 iterations in 4.887s
% 5.08/5.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.08/5.35  % SZS output start Refutation
% 5.08/5.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.08/5.35  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.08/5.35  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.08/5.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.08/5.35  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.08/5.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.08/5.35  thf(sk_A_type, type, sk_A: $i).
% 5.08/5.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.08/5.35  thf(t2_tarski, axiom,
% 5.08/5.35    (![A:$i,B:$i]:
% 5.08/5.35     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 5.08/5.35       ( ( A ) = ( B ) ) ))).
% 5.08/5.35  thf('0', plain,
% 5.08/5.35      (![X3 : $i, X4 : $i]:
% 5.08/5.35         (((X4) = (X3))
% 5.08/5.35          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 5.08/5.35          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 5.08/5.35      inference('cnf', [status(esa)], [t2_tarski])).
% 5.08/5.35  thf('1', plain,
% 5.08/5.35      (![X3 : $i, X4 : $i]:
% 5.08/5.35         (((X4) = (X3))
% 5.08/5.35          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 5.08/5.35          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 5.08/5.35      inference('cnf', [status(esa)], [t2_tarski])).
% 5.08/5.35  thf(t8_subset_1, conjecture,
% 5.08/5.35    (![A:$i,B:$i]:
% 5.08/5.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.08/5.35       ( ![C:$i]:
% 5.08/5.35         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.08/5.35           ( ( ![D:$i]:
% 5.08/5.35               ( ( m1_subset_1 @ D @ A ) =>
% 5.08/5.35                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 5.08/5.35             ( ( B ) = ( C ) ) ) ) ) ))).
% 5.08/5.35  thf(zf_stmt_0, negated_conjecture,
% 5.08/5.35    (~( ![A:$i,B:$i]:
% 5.08/5.35        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.08/5.35          ( ![C:$i]:
% 5.08/5.35            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.08/5.35              ( ( ![D:$i]:
% 5.08/5.35                  ( ( m1_subset_1 @ D @ A ) =>
% 5.08/5.35                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 5.08/5.35                ( ( B ) = ( C ) ) ) ) ) ) )),
% 5.08/5.35    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 5.08/5.35  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf(l3_subset_1, axiom,
% 5.08/5.35    (![A:$i,B:$i]:
% 5.08/5.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.08/5.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.08/5.35  thf('3', plain,
% 5.08/5.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.08/5.35         (~ (r2_hidden @ X8 @ X9)
% 5.08/5.35          | (r2_hidden @ X8 @ X10)
% 5.08/5.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.08/5.35      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.08/5.35  thf('4', plain,
% 5.08/5.35      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 5.08/5.35      inference('sup-', [status(thm)], ['2', '3'])).
% 5.08/5.35  thf('5', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 5.08/5.35          | ((X0) = (sk_C_1))
% 5.08/5.35          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_A))),
% 5.08/5.35      inference('sup-', [status(thm)], ['1', '4'])).
% 5.08/5.35  thf(d2_subset_1, axiom,
% 5.08/5.35    (![A:$i,B:$i]:
% 5.08/5.35     ( ( ( v1_xboole_0 @ A ) =>
% 5.08/5.35         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 5.08/5.35       ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.08/5.35         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 5.08/5.35  thf('6', plain,
% 5.08/5.35      (![X5 : $i, X6 : $i]:
% 5.08/5.35         (~ (r2_hidden @ X5 @ X6)
% 5.08/5.35          | (m1_subset_1 @ X5 @ X6)
% 5.08/5.35          | (v1_xboole_0 @ X6))),
% 5.08/5.35      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.08/5.35  thf(d1_xboole_0, axiom,
% 5.08/5.35    (![A:$i]:
% 5.08/5.35     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.08/5.35  thf('7', plain,
% 5.08/5.35      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.08/5.35      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.08/5.35  thf('8', plain,
% 5.08/5.35      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 5.08/5.35      inference('clc', [status(thm)], ['6', '7'])).
% 5.08/5.35  thf('9', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         (((X0) = (sk_C_1))
% 5.08/5.35          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 5.08/5.35          | (m1_subset_1 @ (sk_C @ sk_C_1 @ X0) @ sk_A))),
% 5.08/5.35      inference('sup-', [status(thm)], ['5', '8'])).
% 5.08/5.35  thf('10', plain,
% 5.08/5.35      (![X11 : $i]:
% 5.08/5.35         (~ (r2_hidden @ X11 @ sk_C_1)
% 5.08/5.35          | (r2_hidden @ X11 @ sk_B_1)
% 5.08/5.35          | ~ (m1_subset_1 @ X11 @ sk_A))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf('11', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 5.08/5.35          | ((X0) = (sk_C_1))
% 5.08/5.35          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B_1)
% 5.08/5.35          | ~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_C_1))),
% 5.08/5.35      inference('sup-', [status(thm)], ['9', '10'])).
% 5.08/5.35  thf('12', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 5.08/5.35          | ((X0) = (sk_C_1))
% 5.08/5.35          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B_1)
% 5.08/5.35          | ((X0) = (sk_C_1))
% 5.08/5.35          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0))),
% 5.08/5.35      inference('sup-', [status(thm)], ['0', '11'])).
% 5.08/5.35  thf('13', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B_1)
% 5.08/5.35          | ((X0) = (sk_C_1))
% 5.08/5.35          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0))),
% 5.08/5.35      inference('simplify', [status(thm)], ['12'])).
% 5.08/5.35  thf('14', plain,
% 5.08/5.35      ((((sk_B_1) = (sk_C_1)) | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_B_1))),
% 5.08/5.35      inference('eq_fact', [status(thm)], ['13'])).
% 5.08/5.35  thf('15', plain, (((sk_B_1) != (sk_C_1))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf('16', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 5.08/5.35      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 5.08/5.35  thf('17', plain,
% 5.08/5.35      (![X3 : $i, X4 : $i]:
% 5.08/5.35         (((X4) = (X3))
% 5.08/5.35          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 5.08/5.35          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 5.08/5.35      inference('cnf', [status(esa)], [t2_tarski])).
% 5.08/5.35  thf('18', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf('19', plain,
% 5.08/5.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.08/5.35         (~ (r2_hidden @ X8 @ X9)
% 5.08/5.35          | (r2_hidden @ X8 @ X10)
% 5.08/5.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.08/5.35      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.08/5.35  thf('20', plain,
% 5.08/5.35      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 5.08/5.35      inference('sup-', [status(thm)], ['18', '19'])).
% 5.08/5.35  thf('21', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ X0)
% 5.08/5.35          | ((sk_B_1) = (X0))
% 5.08/5.35          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 5.08/5.35      inference('sup-', [status(thm)], ['17', '20'])).
% 5.08/5.35  thf('22', plain,
% 5.08/5.35      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 5.08/5.35      inference('clc', [status(thm)], ['6', '7'])).
% 5.08/5.35  thf('23', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         (((sk_B_1) = (X0))
% 5.08/5.35          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ X0)
% 5.08/5.35          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 5.08/5.35      inference('sup-', [status(thm)], ['21', '22'])).
% 5.08/5.35  thf('24', plain,
% 5.08/5.35      (![X3 : $i, X4 : $i]:
% 5.08/5.35         (((X4) = (X3))
% 5.08/5.35          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 5.08/5.35          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 5.08/5.35      inference('cnf', [status(esa)], [t2_tarski])).
% 5.08/5.35  thf('25', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         ((m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A)
% 5.08/5.35          | ((sk_B_1) = (X0))
% 5.08/5.35          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1)
% 5.08/5.35          | ((sk_B_1) = (X0)))),
% 5.08/5.35      inference('sup-', [status(thm)], ['23', '24'])).
% 5.08/5.35  thf('26', plain,
% 5.08/5.35      (![X0 : $i]:
% 5.08/5.35         (~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1)
% 5.08/5.35          | ((sk_B_1) = (X0))
% 5.08/5.35          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 5.08/5.35      inference('simplify', [status(thm)], ['25'])).
% 5.08/5.35  thf('27', plain,
% 5.08/5.35      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_A) | ((sk_B_1) = (sk_C_1)))),
% 5.08/5.35      inference('sup-', [status(thm)], ['16', '26'])).
% 5.08/5.35  thf('28', plain, (((sk_B_1) != (sk_C_1))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf('29', plain, ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_A)),
% 5.08/5.35      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 5.08/5.35  thf('30', plain,
% 5.08/5.35      (![X11 : $i]:
% 5.08/5.35         (~ (r2_hidden @ X11 @ sk_B_1)
% 5.08/5.35          | (r2_hidden @ X11 @ sk_C_1)
% 5.08/5.35          | ~ (m1_subset_1 @ X11 @ sk_A))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf('31', plain,
% 5.08/5.35      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_C_1)
% 5.08/5.35        | ~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_B_1))),
% 5.08/5.35      inference('sup-', [status(thm)], ['29', '30'])).
% 5.08/5.35  thf('32', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 5.08/5.35      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 5.08/5.35  thf('33', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_C_1)),
% 5.08/5.35      inference('demod', [status(thm)], ['31', '32'])).
% 5.08/5.35  thf('34', plain,
% 5.08/5.35      (![X3 : $i, X4 : $i]:
% 5.08/5.35         (((X4) = (X3))
% 5.08/5.35          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 5.08/5.35          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 5.08/5.35      inference('cnf', [status(esa)], [t2_tarski])).
% 5.08/5.35  thf('35', plain,
% 5.08/5.35      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 5.08/5.35        | ((sk_B_1) = (sk_C_1)))),
% 5.08/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.08/5.35  thf('36', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 5.08/5.35      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 5.08/5.35  thf('37', plain, (((sk_B_1) = (sk_C_1))),
% 5.08/5.35      inference('demod', [status(thm)], ['35', '36'])).
% 5.08/5.35  thf('38', plain, (((sk_B_1) != (sk_C_1))),
% 5.08/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.08/5.35  thf('39', plain, ($false),
% 5.08/5.35      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 5.08/5.35  
% 5.08/5.35  % SZS output end Refutation
% 5.08/5.35  
% 5.08/5.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
