%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0PNbcqGvQM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  283 ( 415 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X17 @ X18 ) @ X19 )
        = ( k2_wellord1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_wellord1 @ sk_C_1 @ sk_A )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ( k2_wellord1 @ sk_C_1 @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0PNbcqGvQM
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 123 iterations in 0.066s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.52  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.19/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(d4_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.52       ( ![D:$i]:
% 0.19/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.52         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.19/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.19/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.19/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.52      inference('eq_fact', [status(thm)], ['0'])).
% 0.19/0.52  thf(t29_wellord1, conjecture,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ C ) =>
% 0.19/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.52         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.19/0.52           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.52        ( ( v1_relat_1 @ C ) =>
% 0.19/0.52          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.52            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.19/0.52              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.19/0.52  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d3_tarski, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.52          | (r2_hidden @ X0 @ X2)
% 0.19/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 0.19/0.52          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.19/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.52      inference('eq_fact', [status(thm)], ['0'])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.52         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.19/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.19/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.19/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.52      inference('eq_fact', [status(thm)], ['0'])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.19/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.19/0.52      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.19/0.52        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '11'])).
% 0.19/0.52  thf('13', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.52  thf(t26_wellord1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ C ) =>
% 0.19/0.52       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.19/0.52         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.52         (((k2_wellord1 @ (k2_wellord1 @ X17 @ X18) @ X19)
% 0.19/0.52            = (k2_wellord1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 0.19/0.52          | ~ (v1_relat_1 @ X17))),
% 0.19/0.52      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.19/0.52            = (k2_wellord1 @ X0 @ sk_A))
% 0.19/0.52          | ~ (v1_relat_1 @ X0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (((k2_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.19/0.52         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))
% 0.19/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.52  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
