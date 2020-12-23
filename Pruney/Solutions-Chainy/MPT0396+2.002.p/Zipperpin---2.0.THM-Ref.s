%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bp0R8IyR6K

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:54 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  346 ( 437 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t18_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( sk_D @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_setfam_1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('11',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_setfam_1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('25',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bp0R8IyR6K
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.27/2.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.27/2.53  % Solved by: fo/fo7.sh
% 2.27/2.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.27/2.53  % done 819 iterations in 2.078s
% 2.27/2.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.27/2.53  % SZS output start Refutation
% 2.27/2.53  thf(sk_A_type, type, sk_A: $i).
% 2.27/2.53  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 2.27/2.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.27/2.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.27/2.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.27/2.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.27/2.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.27/2.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.27/2.53  thf(sk_B_type, type, sk_B: $i).
% 2.27/2.53  thf(t18_setfam_1, conjecture,
% 2.27/2.53    (![A:$i,B:$i]:
% 2.27/2.53     ( ( r1_setfam_1 @ A @ B ) =>
% 2.27/2.53       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 2.27/2.53  thf(zf_stmt_0, negated_conjecture,
% 2.27/2.53    (~( ![A:$i,B:$i]:
% 2.27/2.53        ( ( r1_setfam_1 @ A @ B ) =>
% 2.27/2.53          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 2.27/2.53    inference('cnf.neg', [status(esa)], [t18_setfam_1])).
% 2.27/2.53  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 2.27/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.53  thf(d3_tarski, axiom,
% 2.27/2.53    (![A:$i,B:$i]:
% 2.27/2.53     ( ( r1_tarski @ A @ B ) <=>
% 2.27/2.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.27/2.53  thf('1', plain,
% 2.27/2.53      (![X1 : $i, X3 : $i]:
% 2.27/2.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.27/2.53      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.53  thf('2', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 2.27/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.53  thf(t94_zfmisc_1, axiom,
% 2.27/2.53    (![A:$i,B:$i]:
% 2.27/2.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 2.27/2.53       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 2.27/2.53  thf('3', plain,
% 2.27/2.53      (![X6 : $i, X7 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 2.27/2.53          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 2.27/2.53      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.27/2.53  thf(d2_setfam_1, axiom,
% 2.27/2.53    (![A:$i,B:$i]:
% 2.27/2.53     ( ( r1_setfam_1 @ A @ B ) <=>
% 2.27/2.53       ( ![C:$i]:
% 2.27/2.53         ( ~( ( r2_hidden @ C @ A ) & 
% 2.27/2.53              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 2.27/2.53  thf('4', plain,
% 2.27/2.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.27/2.53         ((r1_tarski @ X8 @ (sk_D @ X8 @ X9))
% 2.27/2.53          | ~ (r2_hidden @ X8 @ X10)
% 2.27/2.53          | ~ (r1_setfam_1 @ X10 @ X9))),
% 2.27/2.53      inference('cnf', [status(esa)], [d2_setfam_1])).
% 2.27/2.53  thf('5', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 2.27/2.53          | ~ (r1_setfam_1 @ X0 @ X2)
% 2.27/2.53          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ (sk_D @ (sk_C_1 @ X1 @ X0) @ X2)))),
% 2.27/2.53      inference('sup-', [status(thm)], ['3', '4'])).
% 2.27/2.53  thf('6', plain,
% 2.27/2.53      (![X0 : $i]:
% 2.27/2.53         ((r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ 
% 2.27/2.53           (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B))
% 2.27/2.53          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.27/2.53      inference('sup-', [status(thm)], ['2', '5'])).
% 2.27/2.53  thf('7', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.53         (~ (r2_hidden @ X0 @ X1)
% 2.27/2.53          | (r2_hidden @ X0 @ X2)
% 2.27/2.53          | ~ (r1_tarski @ X1 @ X2))),
% 2.27/2.53      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.53  thf('8', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.27/2.53          | (r2_hidden @ X1 @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B))
% 2.27/2.53          | ~ (r2_hidden @ X1 @ (sk_C_1 @ X0 @ sk_A)))),
% 2.27/2.53      inference('sup-', [status(thm)], ['6', '7'])).
% 2.27/2.53  thf('9', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i]:
% 2.27/2.53         ((r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 2.27/2.53          | (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0 @ sk_A)) @ 
% 2.27/2.53             (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B))
% 2.27/2.53          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.27/2.53      inference('sup-', [status(thm)], ['1', '8'])).
% 2.27/2.53  thf('10', plain,
% 2.27/2.53      (![X6 : $i, X7 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 2.27/2.53          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 2.27/2.53      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.27/2.53  thf('11', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 2.27/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.53  thf('12', plain,
% 2.27/2.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.27/2.53         ((r2_hidden @ (sk_D @ X8 @ X9) @ X9)
% 2.27/2.53          | ~ (r2_hidden @ X8 @ X10)
% 2.27/2.53          | ~ (r1_setfam_1 @ X10 @ X9))),
% 2.27/2.53      inference('cnf', [status(esa)], [d2_setfam_1])).
% 2.27/2.53  thf('13', plain,
% 2.27/2.53      (![X0 : $i]:
% 2.27/2.53         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B))),
% 2.27/2.53      inference('sup-', [status(thm)], ['11', '12'])).
% 2.27/2.53  thf('14', plain,
% 2.27/2.53      (![X0 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.27/2.53          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 2.27/2.53      inference('sup-', [status(thm)], ['10', '13'])).
% 2.27/2.53  thf(l49_zfmisc_1, axiom,
% 2.27/2.53    (![A:$i,B:$i]:
% 2.27/2.53     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.27/2.53  thf('15', plain,
% 2.27/2.53      (![X4 : $i, X5 : $i]:
% 2.27/2.53         ((r1_tarski @ X4 @ (k3_tarski @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 2.27/2.53      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 2.27/2.53  thf('16', plain,
% 2.27/2.53      (![X0 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.27/2.53          | (r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 2.27/2.53             (k3_tarski @ sk_B)))),
% 2.27/2.53      inference('sup-', [status(thm)], ['14', '15'])).
% 2.27/2.53  thf('17', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.53         (~ (r2_hidden @ X0 @ X1)
% 2.27/2.53          | (r2_hidden @ X0 @ X2)
% 2.27/2.53          | ~ (r1_tarski @ X1 @ X2))),
% 2.27/2.53      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.53  thf('18', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.27/2.53          | (r2_hidden @ X1 @ (k3_tarski @ sk_B))
% 2.27/2.53          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B)))),
% 2.27/2.53      inference('sup-', [status(thm)], ['16', '17'])).
% 2.27/2.53  thf('19', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.27/2.53          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 2.27/2.53          | (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0 @ sk_A)) @ 
% 2.27/2.53             (k3_tarski @ sk_B))
% 2.27/2.53          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.27/2.53      inference('sup-', [status(thm)], ['9', '18'])).
% 2.27/2.53  thf('20', plain,
% 2.27/2.53      (![X0 : $i, X1 : $i]:
% 2.27/2.53         ((r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0 @ sk_A)) @ (k3_tarski @ sk_B))
% 2.27/2.53          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 2.27/2.53          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.27/2.53      inference('simplify', [status(thm)], ['19'])).
% 2.27/2.53  thf('21', plain,
% 2.27/2.53      (![X1 : $i, X3 : $i]:
% 2.27/2.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.27/2.53      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.53  thf('22', plain,
% 2.27/2.53      (![X0 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.27/2.53          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ (k3_tarski @ sk_B))
% 2.27/2.53          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ (k3_tarski @ sk_B)))),
% 2.27/2.53      inference('sup-', [status(thm)], ['20', '21'])).
% 2.27/2.53  thf('23', plain,
% 2.27/2.53      (![X0 : $i]:
% 2.27/2.53         ((r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ (k3_tarski @ sk_B))
% 2.27/2.53          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.27/2.53      inference('simplify', [status(thm)], ['22'])).
% 2.27/2.53  thf('24', plain,
% 2.27/2.53      (![X6 : $i, X7 : $i]:
% 2.27/2.53         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 2.27/2.53          | ~ (r1_tarski @ (sk_C_1 @ X7 @ X6) @ X7))),
% 2.27/2.53      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.27/2.53  thf('25', plain,
% 2.27/2.53      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 2.27/2.53        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 2.27/2.53      inference('sup-', [status(thm)], ['23', '24'])).
% 2.27/2.53  thf('26', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 2.27/2.53      inference('simplify', [status(thm)], ['25'])).
% 2.27/2.53  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 2.27/2.53  
% 2.27/2.53  % SZS output end Refutation
% 2.27/2.53  
% 2.38/2.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
