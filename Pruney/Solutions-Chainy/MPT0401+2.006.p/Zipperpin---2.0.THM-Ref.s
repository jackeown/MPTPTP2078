%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UzCEY88h6U

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  193 ( 255 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('3',plain,(
    ! [X30: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_setfam_1 @ X34 @ X35 )
      | ( r2_hidden @ ( sk_C @ X35 @ X34 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k3_tarski @ X29 ) )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( r1_setfam_1 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r1_setfam_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( r1_tarski @ ( sk_C @ X35 @ X34 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_setfam_1 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_setfam_1 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r1_setfam_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['2','10'])).

thf(t23_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_setfam_1 @ A @ B )
        & ( r1_setfam_1 @ B @ C ) )
     => ( r1_setfam_1 @ A @ C ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_setfam_1 @ X39 @ X40 )
      | ~ ( r1_setfam_1 @ X40 @ X41 )
      | ( r1_setfam_1 @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t23_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ ( k1_tarski @ sk_C_1 ) @ X0 )
      | ~ ( r1_setfam_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_setfam_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X37 ) @ ( k3_tarski @ X38 ) )
      | ~ ( r1_setfam_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('16',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ sk_C_1 ) ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X30: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('18',plain,(
    ! [X30: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UzCEY88h6U
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 45 iterations in 0.024s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(t24_setfam_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.50          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.20/0.50  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t31_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.50  thf('3', plain, (![X30 : $i]: ((k3_tarski @ (k1_tarski @ X30)) = (X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.50  thf(d2_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X34 @ X35) | (r2_hidden @ (sk_C @ X35 @ X34) @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf(l49_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i]:
% 0.20/0.50         ((r1_tarski @ X28 @ (k3_tarski @ X29)) | ~ (r2_hidden @ X28 @ X29))),
% 0.20/0.50      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0)
% 0.20/0.50          | (r1_setfam_1 @ (k1_tarski @ X0) @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X34 @ X35)
% 0.20/0.50          | ~ (r2_hidden @ X36 @ X35)
% 0.20/0.50          | ~ (r1_tarski @ (sk_C @ X35 @ X34) @ X36))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ (k1_tarski @ X0) @ X1)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r1_setfam_1 @ (k1_tarski @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1) | (r1_setfam_1 @ (k1_tarski @ X0) @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.50  thf('11', plain, ((r1_setfam_1 @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.50  thf(t23_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.20/0.50       ( r1_setfam_1 @ A @ C ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.50         (~ (r1_setfam_1 @ X39 @ X40)
% 0.20/0.50          | ~ (r1_setfam_1 @ X40 @ X41)
% 0.20/0.50          | (r1_setfam_1 @ X39 @ X41))),
% 0.20/0.50      inference('cnf', [status(esa)], [t23_setfam_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ (k1_tarski @ sk_C_1) @ X0)
% 0.20/0.50          | ~ (r1_setfam_1 @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((r1_setfam_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '13'])).
% 0.20/0.50  thf(t18_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X37 : $i, X38 : $i]:
% 0.20/0.50         ((r1_tarski @ (k3_tarski @ X37) @ (k3_tarski @ X38))
% 0.20/0.50          | ~ (r1_setfam_1 @ X37 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((r1_tarski @ (k3_tarski @ (k1_tarski @ sk_C_1)) @ 
% 0.20/0.50        (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, (![X30 : $i]: ((k3_tarski @ (k1_tarski @ X30)) = (X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.50  thf('18', plain, (![X30 : $i]: ((k3_tarski @ (k1_tarski @ X30)) = (X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.50  thf('19', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.50  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
