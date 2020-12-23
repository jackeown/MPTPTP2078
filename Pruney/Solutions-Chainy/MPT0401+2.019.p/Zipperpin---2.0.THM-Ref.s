%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2BxcH6Psb8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 181 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

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

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t17_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_setfam_1 @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_setfam_1 @ X36 @ X37 )
      | ~ ( r1_setfam_1 @ X37 @ X38 )
      | ( r1_setfam_1 @ X36 @ X38 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X34 ) @ ( k3_tarski @ X35 ) )
      | ~ ( r1_setfam_1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('11',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('13',plain,(
    ! [X28: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('14',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2BxcH6Psb8
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 22 iterations in 0.008s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.22/0.46  thf(t24_setfam_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.22/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.22/0.46          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.22/0.46  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('2', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t37_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X29 : $i, X31 : $i]:
% 0.22/0.46         ((r1_tarski @ (k1_tarski @ X29) @ X31) | ~ (r2_hidden @ X29 @ X31))),
% 0.22/0.46      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.22/0.46  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ sk_B)),
% 0.22/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf(t17_setfam_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X32 : $i, X33 : $i]:
% 0.22/0.46         ((r1_setfam_1 @ X32 @ X33) | ~ (r1_tarski @ X32 @ X33))),
% 0.22/0.46      inference('cnf', [status(esa)], [t17_setfam_1])).
% 0.22/0.46  thf('6', plain, ((r1_setfam_1 @ (k1_tarski @ sk_C) @ sk_B)),
% 0.22/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(t23_setfam_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.22/0.46       ( r1_setfam_1 @ A @ C ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.46         (~ (r1_setfam_1 @ X36 @ X37)
% 0.22/0.46          | ~ (r1_setfam_1 @ X37 @ X38)
% 0.22/0.46          | (r1_setfam_1 @ X36 @ X38))),
% 0.22/0.46      inference('cnf', [status(esa)], [t23_setfam_1])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         ((r1_setfam_1 @ (k1_tarski @ sk_C) @ X0) | ~ (r1_setfam_1 @ sk_B @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain, ((r1_setfam_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.22/0.46  thf(t18_setfam_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r1_setfam_1 @ A @ B ) =>
% 0.22/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X34 : $i, X35 : $i]:
% 0.22/0.46         ((r1_tarski @ (k3_tarski @ X34) @ (k3_tarski @ X35))
% 0.22/0.46          | ~ (r1_setfam_1 @ X34 @ X35))),
% 0.22/0.46      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      ((r1_tarski @ (k3_tarski @ (k1_tarski @ sk_C)) @ 
% 0.22/0.46        (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf(t31_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.46  thf('12', plain, (![X28 : $i]: ((k3_tarski @ (k1_tarski @ X28)) = (X28))),
% 0.22/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.22/0.46  thf('13', plain, (![X28 : $i]: ((k3_tarski @ (k1_tarski @ X28)) = (X28))),
% 0.22/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.22/0.46  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.22/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.46  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
