%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZKtd3DCSs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  112 ( 130 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ B @ A )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('1',plain,(
    ! [X8: $i] :
      ( ( r2_hidden @ X8 @ sk_A )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t35_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( v3_ordinal1 @ B ) )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X4 ) )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( v3_ordinal1 @ X7 )
      | ~ ( r2_hidden @ X7 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X4 ) )
      | ~ ( v3_ordinal1 @ ( sk_B @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('13',plain,(
    v3_ordinal1 @ ( k3_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['8','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZKtd3DCSs
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:12:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 17 iterations in 0.011s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.45  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.45  thf(t29_ordinal1, axiom,
% 0.22/0.45    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.22/0.45  thf('0', plain,
% 0.22/0.45      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.45  thf(t37_ordinal1, conjecture,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]:
% 0.22/0.45        ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t37_ordinal1])).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X8 : $i]: ((r2_hidden @ X8 @ sk_A) | ~ (v3_ordinal1 @ X8))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(t92_zfmisc_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((r1_tarski @ X0 @ (k3_tarski @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [t92_zfmisc_1])).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v3_ordinal1 @ X0) | (r1_tarski @ X0 @ (k3_tarski @ sk_A)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.45  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.22/0.45  thf('4', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_ordinal1 @ X2))),
% 0.22/0.45      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.22/0.45  thf(t7_ordinal1, axiom,
% 0.22/0.45    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 0.22/0.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.45  thf('6', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.22/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.45  thf('7', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ (k3_tarski @ sk_A)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.45  thf('8', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.22/0.45      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.45  thf(t35_ordinal1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) =>
% 0.22/0.45       ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.22/0.45  thf('9', plain,
% 0.22/0.45      (![X4 : $i]:
% 0.22/0.45         ((v3_ordinal1 @ (k3_tarski @ X4)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.45      inference('cnf', [status(esa)], [t35_ordinal1])).
% 0.22/0.45  thf('10', plain,
% 0.22/0.45      (![X7 : $i]: ((v3_ordinal1 @ X7) | ~ (r2_hidden @ X7 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      (((v3_ordinal1 @ (k3_tarski @ sk_A)) | (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.45  thf('12', plain,
% 0.22/0.45      (![X4 : $i]:
% 0.22/0.45         ((v3_ordinal1 @ (k3_tarski @ X4)) | ~ (v3_ordinal1 @ (sk_B @ X4)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t35_ordinal1])).
% 0.22/0.45  thf('13', plain, ((v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.22/0.45      inference('clc', [status(thm)], ['11', '12'])).
% 0.22/0.45  thf('14', plain, ($false), inference('demod', [status(thm)], ['8', '13'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
