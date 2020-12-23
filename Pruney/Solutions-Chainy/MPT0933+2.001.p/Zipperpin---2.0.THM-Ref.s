%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lt5uQ5fb0C

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  39 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  137 ( 401 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t94_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r2_hidden @ A @ B )
            & ( ( k1_mcart_1 @ C )
              = ( k1_mcart_1 @ A ) )
            & ( ( k2_mcart_1 @ C )
              = ( k2_mcart_1 @ A ) ) )
         => ( C = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ A @ B )
              & ( ( k1_mcart_1 @ C )
                = ( k1_mcart_1 @ A ) )
              & ( ( k2_mcart_1 @ C )
                = ( k2_mcart_1 @ A ) ) )
           => ( C = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_mcart_1 @ sk_C )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_mcart_1 @ sk_C )
    = ( k2_mcart_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_C
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    sk_C = sk_A ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    sk_C != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lt5uQ5fb0C
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 8 iterations in 0.007s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.45  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.45  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.45  thf(t94_mcart_1, conjecture,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ B ) =>
% 0.22/0.45       ( ![C:$i]:
% 0.22/0.45         ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ A @ B ) & 
% 0.22/0.45             ( ( k1_mcart_1 @ C ) = ( k1_mcart_1 @ A ) ) & 
% 0.22/0.45             ( ( k2_mcart_1 @ C ) = ( k2_mcart_1 @ A ) ) ) =>
% 0.22/0.45           ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i,B:$i]:
% 0.22/0.45        ( ( v1_relat_1 @ B ) =>
% 0.22/0.45          ( ![C:$i]:
% 0.22/0.45            ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ A @ B ) & 
% 0.22/0.45                ( ( k1_mcart_1 @ C ) = ( k1_mcart_1 @ A ) ) & 
% 0.22/0.45                ( ( k2_mcart_1 @ C ) = ( k2_mcart_1 @ A ) ) ) =>
% 0.22/0.45              ( ( C ) = ( A ) ) ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t94_mcart_1])).
% 0.22/0.45  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(t23_mcart_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ B ) =>
% 0.22/0.45       ( ( r2_hidden @ A @ B ) =>
% 0.22/0.45         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0)))
% 0.22/0.45          | ~ (v1_relat_1 @ X1)
% 0.22/0.45          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.45        | ((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A))))),
% 0.22/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.45  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('4', plain,
% 0.22/0.45      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.22/0.45      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.45  thf('5', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('6', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0)))
% 0.22/0.45          | ~ (v1_relat_1 @ X1)
% 0.22/0.45          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.22/0.45  thf('7', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.45        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.22/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.45  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('9', plain, (((k1_mcart_1 @ sk_C) = (k1_mcart_1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('10', plain, (((k2_mcart_1 @ sk_C) = (k2_mcart_1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      (((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.22/0.45      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.22/0.45  thf('12', plain, (((sk_C) = (sk_A))),
% 0.22/0.45      inference('sup+', [status(thm)], ['4', '11'])).
% 0.22/0.45  thf('13', plain, (((sk_C) != (sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('14', plain, ($false),
% 0.22/0.45      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
