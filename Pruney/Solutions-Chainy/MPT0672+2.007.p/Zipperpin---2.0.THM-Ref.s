%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHZzw5X5CE

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:58 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  45 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  288 ( 624 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :   12 (   6 average)

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

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t97_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) )
          & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
              = ( k8_relat_1 @ A @ C ) )
            & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
              = ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ X4 @ X5 ) )
        = ( k8_relat_1 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ X2 ) )
        = ( k8_relat_1 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( ( ( k8_relat_1 @ sk_A @ sk_C )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
    = ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['4','14'])).

thf('16',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHZzw5X5CE
% 0.16/0.38  % Computer   : n020.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 12:34:52 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.47  % Solved by: fo/fo7.sh
% 0.23/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.47  % done 11 iterations in 0.010s
% 0.23/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.47  % SZS output start Refutation
% 0.23/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.47  thf(t97_funct_1, conjecture,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.23/0.47         ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.23/0.47             ( k8_relat_1 @ A @ C ) ) & 
% 0.23/0.47           ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.23/0.47             ( k8_relat_1 @ A @ C ) ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.47        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.47          ( ( r1_tarski @ A @ B ) =>
% 0.23/0.47            ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.23/0.47                ( k8_relat_1 @ A @ C ) ) & 
% 0.23/0.47              ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.23/0.47                ( k8_relat_1 @ A @ C ) ) ) ) ) )),
% 0.23/0.47    inference('cnf.neg', [status(esa)], [t97_funct_1])).
% 0.23/0.47  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(t130_relat_1, axiom,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( ( v1_relat_1 @ C ) =>
% 0.23/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.23/0.47         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.23/0.47  thf('1', plain,
% 0.23/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.47         (~ (r1_tarski @ X3 @ X4)
% 0.23/0.47          | ~ (v1_relat_1 @ X5)
% 0.23/0.47          | ((k8_relat_1 @ X3 @ (k8_relat_1 @ X4 @ X5))
% 0.23/0.47              = (k8_relat_1 @ X3 @ X5)))),
% 0.23/0.47      inference('cnf', [status(esa)], [t130_relat_1])).
% 0.23/0.47  thf('2', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ X0))
% 0.23/0.47            = (k8_relat_1 @ sk_A @ X0))
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.47  thf('3', plain,
% 0.23/0.47      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47          != (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47        | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.23/0.47            != (k8_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('4', plain,
% 0.23/0.47      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.23/0.47          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.23/0.47         <= (~
% 0.23/0.47             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.23/0.47                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('split', [status(esa)], ['3'])).
% 0.23/0.47  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(t129_relat_1, axiom,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( ( v1_relat_1 @ C ) =>
% 0.23/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.23/0.47         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.23/0.47  thf('6', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.47          | ~ (v1_relat_1 @ X2)
% 0.23/0.47          | ((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ X2))
% 0.23/0.47              = (k8_relat_1 @ X0 @ X2)))),
% 0.23/0.47      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.23/0.47  thf('7', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.23/0.47            = (k8_relat_1 @ sk_A @ X0))
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.47  thf('8', plain,
% 0.23/0.47      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.23/0.47         <= (~
% 0.23/0.47             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('split', [status(esa)], ['3'])).
% 0.23/0.47  thf('9', plain,
% 0.23/0.47      (((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47         | ~ (v1_relat_1 @ sk_C)))
% 0.23/0.47         <= (~
% 0.23/0.47             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.47  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('11', plain,
% 0.23/0.47      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C)))
% 0.23/0.47         <= (~
% 0.23/0.47             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.47  thf('12', plain,
% 0.23/0.47      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.47  thf('13', plain,
% 0.23/0.47      (~
% 0.23/0.47       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.23/0.47          = (k8_relat_1 @ sk_A @ sk_C))) | 
% 0.23/0.47       ~
% 0.23/0.47       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('split', [status(esa)], ['3'])).
% 0.23/0.47  thf('14', plain,
% 0.23/0.47      (~
% 0.23/0.47       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.23/0.47          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.23/0.47  thf('15', plain,
% 0.23/0.47      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.23/0.47         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.23/0.47      inference('simpl_trail', [status(thm)], ['4', '14'])).
% 0.23/0.47  thf('16', plain,
% 0.23/0.47      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.23/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.23/0.47      inference('sup-', [status(thm)], ['2', '15'])).
% 0.23/0.47  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('18', plain,
% 0.23/0.47      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.23/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.47  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
