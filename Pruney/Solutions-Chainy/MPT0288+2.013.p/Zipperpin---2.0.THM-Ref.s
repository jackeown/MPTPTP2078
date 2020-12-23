%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.is9abvrl3d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 206 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t95_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X3 ) @ X5 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k1_tarski @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.is9abvrl3d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:57:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 22 iterations in 0.012s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.43  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.43  thf(t95_zfmisc_1, conjecture,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.43       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (~( ![A:$i,B:$i]:
% 0.21/0.43        ( ( r1_tarski @ A @ B ) =>
% 0.21/0.43          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.21/0.43    inference('cnf.neg', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.43  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf(t94_zfmisc_1, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.21/0.43       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.43  thf('2', plain,
% 0.21/0.43      (![X8 : $i, X9 : $i]:
% 0.21/0.43         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 0.21/0.43          | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.21/0.43      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.43  thf(l1_zfmisc_1, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.43  thf('3', plain,
% 0.21/0.43      (![X3 : $i, X5 : $i]:
% 0.21/0.43         ((r1_tarski @ (k1_tarski @ X3) @ X5) | ~ (r2_hidden @ X3 @ X5))),
% 0.21/0.43      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.43  thf('4', plain,
% 0.21/0.43      (![X0 : $i, X1 : $i]:
% 0.21/0.43         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.43          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.21/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.43  thf(t1_xboole_1, axiom,
% 0.21/0.43    (![A:$i,B:$i,C:$i]:
% 0.21/0.43     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.43       ( r1_tarski @ A @ C ) ))).
% 0.21/0.43  thf('5', plain,
% 0.21/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.43         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.43          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.43          | (r1_tarski @ X0 @ X2))),
% 0.21/0.43      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.43  thf('6', plain,
% 0.21/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.43         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.43          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X2)
% 0.21/0.43          | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.43      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.43  thf('7', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.21/0.43          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 0.21/0.43      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.43  thf('8', plain,
% 0.21/0.43      (![X3 : $i, X4 : $i]:
% 0.21/0.43         ((r2_hidden @ X3 @ X4) | ~ (r1_tarski @ (k1_tarski @ X3) @ X4))),
% 0.21/0.43      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.43  thf('9', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.21/0.43          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.21/0.43      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.43  thf(l49_zfmisc_1, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.43  thf('10', plain,
% 0.21/0.43      (![X6 : $i, X7 : $i]:
% 0.21/0.43         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.43      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.43  thf('11', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.21/0.43          | (r1_tarski @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.43  thf('12', plain,
% 0.21/0.43      (![X8 : $i, X9 : $i]:
% 0.21/0.43         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 0.21/0.43          | ~ (r1_tarski @ (sk_C @ X9 @ X8) @ X9))),
% 0.21/0.43      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.43  thf('13', plain,
% 0.21/0.43      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 0.21/0.43        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.43  thf('14', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.21/0.43      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.43  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.43  
% 0.21/0.43  % SZS output end Refutation
% 0.21/0.43  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
