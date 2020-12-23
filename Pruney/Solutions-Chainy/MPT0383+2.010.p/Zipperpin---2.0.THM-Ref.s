%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nfSBmKEsTK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:31 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 ( 577 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t65_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r2_hidden @ D @ C )
          & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ A )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( D
                   != ( k4_tarski @ E @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_subset_1])).

thf('0',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( X13
        = ( k4_tarski @ ( sk_E @ X13 @ X12 @ X11 ) @ ( sk_F @ X13 @ X12 @ X11 ) ) )
      | ~ ( r2_hidden @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( X0
        = ( k4_tarski @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_F @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( sk_D
    = ( k4_tarski @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r2_hidden @ ( sk_F @ X13 @ X12 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ ( sk_F @ sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( sk_F @ sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ sk_B )
      | ( sk_D
       != ( k4_tarski @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_D
       != ( k4_tarski @ X0 @ ( sk_F @ sk_D @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_D != sk_D )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ~ ( m1_subset_1 @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r2_hidden @ ( sk_E @ X13 @ X12 @ X11 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('24',plain,(
    m1_subset_1 @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['17','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nfSBmKEsTK
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:57:59 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 48 iterations in 0.023s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.46  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.18/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.46  thf(t65_subset_1, conjecture,
% 0.18/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.46     ( ~( ( r2_hidden @ D @ C ) & 
% 0.18/0.46          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.18/0.46          ( ![E:$i]:
% 0.18/0.46            ( ( m1_subset_1 @ E @ A ) =>
% 0.18/0.46              ( ![F:$i]:
% 0.18/0.46                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.46        ( ~( ( r2_hidden @ D @ C ) & 
% 0.18/0.46             ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.18/0.46             ( ![E:$i]:
% 0.18/0.46               ( ( m1_subset_1 @ E @ A ) =>
% 0.18/0.46                 ( ![F:$i]:
% 0.18/0.46                   ( ( m1_subset_1 @ F @ B ) =>
% 0.18/0.46                     ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t65_subset_1])).
% 0.18/0.46  thf('0', plain, ((r2_hidden @ sk_D @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('1', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t103_zfmisc_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.46     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.18/0.46          ( r2_hidden @ D @ A ) & 
% 0.18/0.46          ( ![E:$i,F:$i]:
% 0.18/0.46            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.18/0.46                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X11 @ X12))
% 0.18/0.46          | ((X13)
% 0.18/0.46              = (k4_tarski @ (sk_E @ X13 @ X12 @ X11) @ 
% 0.18/0.46                 (sk_F @ X13 @ X12 @ X11)))
% 0.18/0.46          | ~ (r2_hidden @ X13 @ X10))),
% 0.18/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X0 @ sk_C)
% 0.18/0.46          | ((X0)
% 0.18/0.46              = (k4_tarski @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 0.18/0.46                 (sk_F @ X0 @ sk_B @ sk_A))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (((sk_D)
% 0.18/0.46         = (k4_tarski @ (sk_E @ sk_D @ sk_B @ sk_A) @ 
% 0.18/0.46            (sk_F @ sk_D @ sk_B @ sk_A)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.18/0.46  thf('5', plain, ((r2_hidden @ sk_D @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('6', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X11 @ X12))
% 0.18/0.46          | (r2_hidden @ (sk_F @ X13 @ X12 @ X11) @ X12)
% 0.18/0.46          | ~ (r2_hidden @ X13 @ X10))),
% 0.18/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X0 @ sk_C)
% 0.18/0.46          | (r2_hidden @ (sk_F @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.46  thf('9', plain, ((r2_hidden @ (sk_F @ sk_D @ sk_B @ sk_A) @ sk_B)),
% 0.18/0.46      inference('sup-', [status(thm)], ['5', '8'])).
% 0.18/0.46  thf(d2_subset_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( v1_xboole_0 @ A ) =>
% 0.18/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.18/0.46       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (![X14 : $i, X15 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X14 @ X15)
% 0.18/0.46          | (m1_subset_1 @ X14 @ X15)
% 0.18/0.46          | (v1_xboole_0 @ X15))),
% 0.18/0.46      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.18/0.46  thf(t7_boole, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.18/0.46      inference('cnf', [status(esa)], [t7_boole])).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      (![X14 : $i, X15 : $i]:
% 0.18/0.46         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.18/0.46      inference('clc', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf('13', plain, ((m1_subset_1 @ (sk_F @ sk_D @ sk_B @ sk_A) @ sk_B)),
% 0.18/0.46      inference('sup-', [status(thm)], ['9', '12'])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (![X17 : $i, X18 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X17 @ sk_B)
% 0.18/0.46          | ((sk_D) != (k4_tarski @ X18 @ X17))
% 0.18/0.46          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('15', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.18/0.46          | ((sk_D) != (k4_tarski @ X0 @ (sk_F @ sk_D @ sk_B @ sk_A))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.46  thf('16', plain,
% 0.18/0.46      ((((sk_D) != (sk_D))
% 0.18/0.46        | ~ (m1_subset_1 @ (sk_E @ sk_D @ sk_B @ sk_A) @ sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['4', '15'])).
% 0.18/0.46  thf('17', plain, (~ (m1_subset_1 @ (sk_E @ sk_D @ sk_B @ sk_A) @ sk_A)),
% 0.18/0.46      inference('simplify', [status(thm)], ['16'])).
% 0.18/0.46  thf('18', plain, ((r2_hidden @ sk_D @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('19', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X11 @ X12))
% 0.18/0.46          | (r2_hidden @ (sk_E @ X13 @ X12 @ X11) @ X11)
% 0.18/0.46          | ~ (r2_hidden @ X13 @ X10))),
% 0.18/0.46      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X0 @ sk_C)
% 0.18/0.46          | (r2_hidden @ (sk_E @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.18/0.46  thf('22', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_B @ sk_A) @ sk_A)),
% 0.18/0.46      inference('sup-', [status(thm)], ['18', '21'])).
% 0.18/0.46  thf('23', plain,
% 0.18/0.46      (![X14 : $i, X15 : $i]:
% 0.18/0.46         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.18/0.46      inference('clc', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf('24', plain, ((m1_subset_1 @ (sk_E @ sk_D @ sk_B @ sk_A) @ sk_A)),
% 0.18/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.18/0.46  thf('25', plain, ($false), inference('demod', [status(thm)], ['17', '24'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
