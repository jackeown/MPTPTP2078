%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZmVLTOpHCw

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  325 ( 405 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t65_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
        = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_mcart_1])).

thf('0',plain,(
    ( k4_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X29 ) )
      = ( k1_tarski @ ( k4_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X36 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ X0 @ X3 )
      = ( k3_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ X0 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_mcart_1 @ X30 @ X31 @ X32 )
      = ( k4_tarski @ ( k4_tarski @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ X0 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X29 ) )
      = ( k1_tarski @ ( k4_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_mcart_1 @ X30 @ X31 @ X32 )
      = ( k4_tarski @ ( k4_tarski @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_mcart_1 @ X30 @ X31 @ X32 )
      = ( k4_tarski @ ( k4_tarski @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t32_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) )).

thf('16',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_mcart_1 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_mcart_1 @ ( k4_tarski @ X40 @ X41 ) @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t32_mcart_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','11','12','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZmVLTOpHCw
% 0.13/0.37  % Computer   : n023.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 15:28:21 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 35 iterations in 0.030s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(t65_mcart_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k4_zfmisc_1 @
% 0.22/0.51         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ 
% 0.22/0.51         ( k1_tarski @ D ) ) =
% 0.22/0.51       ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51        ( ( k4_zfmisc_1 @
% 0.22/0.51            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ 
% 0.22/0.51            ( k1_tarski @ D ) ) =
% 0.22/0.51          ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t65_mcart_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (((k4_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.22/0.51         (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))
% 0.22/0.51         != (k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t35_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.51       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X28 : $i, X29 : $i]:
% 0.22/0.51         ((k2_zfmisc_1 @ (k1_tarski @ X28) @ (k1_tarski @ X29))
% 0.22/0.51           = (k1_tarski @ (k4_tarski @ X28 @ X29)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.51  thf(d3_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.22/0.51           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.22/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.22/0.51           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.22/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf(d4_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39)
% 0.22/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X36 @ X37 @ X38) @ X39))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ X0 @ X3)
% 0.22/0.51           = (k2_zfmisc_1 @ 
% 0.22/0.51              (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ X0) @ X3))),
% 0.22/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.51         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ X0 @ X3)
% 0.22/0.51           = (k3_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ X0 @ X3))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ (k1_tarski @ X3) @ (k1_tarski @ X2) @ 
% 0.22/0.51           (k1_tarski @ X1) @ X0)
% 0.22/0.51           = (k2_zfmisc_1 @ 
% 0.22/0.51              (k1_tarski @ (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1)) @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '8'])).
% 0.22/0.51  thf(d3_mcart_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.51         ((k3_mcart_1 @ X30 @ X31 @ X32)
% 0.22/0.51           = (k4_tarski @ (k4_tarski @ X30 @ X31) @ X32))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_zfmisc_1 @ (k1_tarski @ X3) @ (k1_tarski @ X2) @ 
% 0.22/0.51           (k1_tarski @ X1) @ X0)
% 0.22/0.51           = (k2_zfmisc_1 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X28 : $i, X29 : $i]:
% 0.22/0.51         ((k2_zfmisc_1 @ (k1_tarski @ X28) @ (k1_tarski @ X29))
% 0.22/0.51           = (k1_tarski @ (k4_tarski @ X28 @ X29)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.51         ((k3_mcart_1 @ X30 @ X31 @ X32)
% 0.22/0.51           = (k4_tarski @ (k4_tarski @ X30 @ X31) @ X32))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.51         ((k3_mcart_1 @ X30 @ X31 @ X32)
% 0.22/0.51           = (k4_tarski @ (k4_tarski @ X30 @ X31) @ X32))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.22/0.51           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf(t32_mcart_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ))).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.51         ((k4_mcart_1 @ X40 @ X41 @ X42 @ X43)
% 0.22/0.51           = (k3_mcart_1 @ (k4_tarski @ X40 @ X41) @ X42 @ X43))),
% 0.22/0.51      inference('cnf', [status(esa)], [t32_mcart_1])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_mcart_1 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k4_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1) @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.22/0.51         != (k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '11', '12', '17'])).
% 0.22/0.51  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
