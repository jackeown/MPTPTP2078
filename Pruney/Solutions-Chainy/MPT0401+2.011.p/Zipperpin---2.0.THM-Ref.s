%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ca6j9Hiqpx

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 235 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ ( k3_tarski @ X33 ) )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X35 ) @ ( k3_tarski @ X36 ) )
      | ~ ( r1_setfam_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('10',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X34: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_A )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ca6j9Hiqpx
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 22 iterations in 0.008s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.43  thf(t24_setfam_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i]:
% 0.20/0.43        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.43          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.20/0.43  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(d3_tarski, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X1 : $i, X3 : $i]:
% 0.20/0.43         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('2', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(l49_zfmisc_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X32 : $i, X33 : $i]:
% 0.20/0.43         ((r1_tarski @ X32 @ (k3_tarski @ X33)) | ~ (r2_hidden @ X32 @ X33))),
% 0.20/0.43      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.43  thf('4', plain, ((r1_tarski @ sk_C_1 @ (k3_tarski @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.43          | (r2_hidden @ X0 @ X2)
% 0.20/0.43          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r2_hidden @ X0 @ (k3_tarski @ sk_B)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k3_tarski @ sk_B)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.43  thf('8', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t18_setfam_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.43       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      (![X35 : $i, X36 : $i]:
% 0.20/0.43         ((r1_tarski @ (k3_tarski @ X35) @ (k3_tarski @ X36))
% 0.20/0.43          | ~ (r1_setfam_1 @ X35 @ X36))),
% 0.20/0.43      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.43  thf(t31_zfmisc_1, axiom,
% 0.20/0.43    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.43  thf('11', plain, (![X34 : $i]: ((k3_tarski @ (k1_tarski @ X34)) = (X34))),
% 0.20/0.43      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.43  thf('12', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.20/0.43      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.43  thf('13', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.43          | (r2_hidden @ X0 @ X2)
% 0.20/0.43          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k3_tarski @ sk_B)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.43  thf('15', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.20/0.43      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X1 : $i, X3 : $i]:
% 0.20/0.43         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      (((r1_tarski @ sk_C_1 @ sk_A) | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.20/0.43      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.43  thf('18', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.20/0.43      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.43  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
