%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c53zY7x62y

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  362 ( 698 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) ) @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( ( k8_relat_1 @ X9 @ ( k8_relat_1 @ X10 @ X11 ) )
        = ( k8_relat_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( ( ( k8_relat_1 @ sk_A @ sk_C )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
    = ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('20',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['10','20'])).

thf('22',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c53zY7x62y
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:57:14 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 26 iterations in 0.036s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(t97_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48         ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.20/0.48             ( k8_relat_1 @ A @ C ) ) & 
% 0.20/0.48           ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.20/0.48             ( k8_relat_1 @ A @ C ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48            ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.20/0.48                ( k8_relat_1 @ A @ C ) ) & 
% 0.20/0.48              ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.20/0.48                ( k8_relat_1 @ A @ C ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t97_funct_1])).
% 0.20/0.48  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t116_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X5 @ X6)) @ X5)
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.20/0.48  thf(t1_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.48       ( r1_tarski @ A @ C ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.48          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.48          | (r1_tarski @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X1)
% 0.20/0.48          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2)
% 0.20/0.48          | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf(t125_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.48         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.20/0.48          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.48          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.48              = (k8_relat_1 @ sk_A @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(dt_k8_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((v1_relat_1 @ (k8_relat_1 @ X3 @ X4)) | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.48            = (k8_relat_1 @ sk_A @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48          != (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48        | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48            != (k8_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t130_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X9 @ X10)
% 0.20/0.48          | ~ (v1_relat_1 @ X11)
% 0.20/0.48          | ((k8_relat_1 @ X9 @ (k8_relat_1 @ X10 @ X11))
% 0.20/0.48              = (k8_relat_1 @ X9 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t130_relat_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ X0))
% 0.20/0.48            = (k8_relat_1 @ sk_A @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48          = (k8_relat_1 @ sk_A @ sk_C))) | 
% 0.20/0.48       ~
% 0.20/0.48       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.48          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['10', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '21'])).
% 0.20/0.48  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
