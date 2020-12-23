%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nPXZFUpX1c

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 181 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r1_tarski @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ B )
           => ( r1_tarski @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t17_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_setfam_1 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t17_setfam_1])).

thf('6',plain,(
    r1_setfam_1 @ ( k1_tarski @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t23_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_setfam_1 @ A @ B )
        & ( r1_setfam_1 @ B @ C ) )
     => ( r1_setfam_1 @ A @ C ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_setfam_1 @ X18 @ X19 )
      | ~ ( r1_setfam_1 @ X19 @ X20 )
      | ( r1_setfam_1 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ ( k1_tarski @ sk_C ) @ X0 )
      | ~ ( r1_setfam_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_setfam_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) )
      | ~ ( r1_setfam_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('11',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('14',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nPXZFUpX1c
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:53:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 22 iterations in 0.012s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(t24_setfam_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.46          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.20/0.46  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(l1_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X10 : $i, X12 : $i]:
% 0.20/0.46         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.46  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t17_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i]:
% 0.20/0.46         ((r1_setfam_1 @ X14 @ X15) | ~ (r1_tarski @ X14 @ X15))),
% 0.20/0.46      inference('cnf', [status(esa)], [t17_setfam_1])).
% 0.20/0.46  thf('6', plain, ((r1_setfam_1 @ (k1_tarski @ sk_C) @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(t23_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.20/0.46       ( r1_setfam_1 @ A @ C ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.46         (~ (r1_setfam_1 @ X18 @ X19)
% 0.20/0.46          | ~ (r1_setfam_1 @ X19 @ X20)
% 0.20/0.46          | (r1_setfam_1 @ X18 @ X20))),
% 0.20/0.46      inference('cnf', [status(esa)], [t23_setfam_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_setfam_1 @ (k1_tarski @ sk_C) @ X0) | ~ (r1_setfam_1 @ sk_B @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, ((r1_setfam_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf(t18_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X16 : $i, X17 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X16) @ (k3_tarski @ X17))
% 0.20/0.46          | ~ (r1_setfam_1 @ X16 @ X17))),
% 0.20/0.46      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((r1_tarski @ (k3_tarski @ (k1_tarski @ sk_C)) @ 
% 0.20/0.46        (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf(t31_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.46  thf('12', plain, (![X13 : $i]: ((k3_tarski @ (k1_tarski @ X13)) = (X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.46  thf('13', plain, (![X13 : $i]: ((k3_tarski @ (k1_tarski @ X13)) = (X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.46  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.46  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
