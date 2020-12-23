%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lm4pqBpNt5

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  45 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  288 ( 624 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t82_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = ( k7_relat_1 @ C @ A ) )
          & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
              = ( k7_relat_1 @ C @ A ) )
            & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
              = ( k7_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X5 @ X4 ) @ X3 )
        = ( k7_relat_1 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( ( ( k7_relat_1 @ sk_C @ sk_A )
       != ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','14'])).

thf('16',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k7_relat_1 @ sk_C @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lm4pqBpNt5
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:55:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 11 iterations in 0.011s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(t82_funct_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48         ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.48             ( k7_relat_1 @ C @ A ) ) & 
% 0.21/0.48           ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.21/0.48             ( k7_relat_1 @ C @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48            ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.48                ( k7_relat_1 @ C @ A ) ) & 
% 0.21/0.48              ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.21/0.48                ( k7_relat_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t82_funct_1])).
% 0.21/0.48  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t103_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.48          | ~ (v1_relat_1 @ X5)
% 0.21/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X5 @ X4) @ X3)
% 0.21/0.48              = (k7_relat_1 @ X5 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.21/0.48            = (k7_relat_1 @ X0 @ sk_A))
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48          != (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.48        | ((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.48            != (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.48          != (k7_relat_1 @ sk_C @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t102_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X2)
% 0.21/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 0.21/0.48              = (k7_relat_1 @ X2 @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 0.21/0.48            = (k7_relat_1 @ X0 @ sk_A))
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48          != (k7_relat_1 @ sk_C @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_C)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.48          = (k7_relat_1 @ sk_C @ sk_A))) | 
% 0.21/0.48       ~
% 0.21/0.48       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.48          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.48          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.48         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['4', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '15'])).
% 0.21/0.48  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
