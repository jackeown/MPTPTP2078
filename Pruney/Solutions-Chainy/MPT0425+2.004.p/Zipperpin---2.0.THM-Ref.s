%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7wGEAtIMvX

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  239 ( 349 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t57_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
        & ! [D: $i] :
            ( ( r2_hidden @ D @ B )
           => ( r1_xboole_0 @ D @ C ) ) )
     => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ B )
             => ( r1_xboole_0 @ D @ C ) ) )
       => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_2 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C_2 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X7 ) @ ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X2 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X2 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k3_tarski @ sk_A ) )
    | ~ ( r1_xboole_0 @ sk_C_2 @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( r1_xboole_0 @ X11 @ sk_C_2 )
      | ~ ( r2_hidden @ X11 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X9 ) @ X10 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_2 )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_2 ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    r1_tarski @ sk_C_2 @ ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['5','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7wGEAtIMvX
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 22 iterations in 0.019s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(t57_setfam_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49         ( ![D:$i]: ( ( r2_hidden @ D @ B ) => ( r1_xboole_0 @ D @ C ) ) ) ) =>
% 0.21/0.49       ( r1_tarski @ C @ ( k3_tarski @ A ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49            ( ![D:$i]: ( ( r2_hidden @ D @ B ) => ( r1_xboole_0 @ D @ C ) ) ) ) =>
% 0.21/0.49          ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t57_setfam_1])).
% 0.21/0.49  thf('0', plain, (~ (r1_tarski @ sk_C_2 @ (k3_tarski @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((r1_tarski @ sk_C_2 @ (k3_tarski @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t96_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_xboole_0 @ X7 @ X8))
% 0.21/0.49           = (k2_xboole_0 @ (k3_tarski @ X7) @ (k3_tarski @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.21/0.49  thf(t73_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.49       ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((r1_tarski @ X4 @ X5)
% 0.21/0.49          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6))
% 0.21/0.49          | ~ (r1_xboole_0 @ X4 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.49          | ~ (r1_xboole_0 @ X2 @ (k3_tarski @ X0))
% 0.21/0.49          | (r1_tarski @ X2 @ (k3_tarski @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r1_tarski @ sk_C_2 @ (k3_tarski @ sk_A))
% 0.21/0.49        | ~ (r1_xboole_0 @ sk_C_2 @ (k3_tarski @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.49  thf(t98_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.21/0.49       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k3_tarski @ X9) @ X10)
% 0.21/0.49          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X11 : $i]: ((r1_xboole_0 @ X11 @ sk_C_2) | ~ (r2_hidden @ X11 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.21/0.49          | (r1_xboole_0 @ (sk_C_1 @ X0 @ sk_B) @ sk_C_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k3_tarski @ X9) @ X10)
% 0.21/0.49          | ~ (r1_xboole_0 @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_2)
% 0.21/0.49        | (r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_2)),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf(t3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.49          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.49          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.49  thf('18', plain, ((r1_xboole_0 @ sk_C_2 @ (k3_tarski @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '17'])).
% 0.21/0.49  thf('19', plain, ((r1_tarski @ sk_C_2 @ (k3_tarski @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '18'])).
% 0.21/0.49  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
