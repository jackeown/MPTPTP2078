%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQLkt4JRaO

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:30 EST 2020

% Result     : Theorem 11.10s
% Output     : Refutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  414 ( 444 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X6 @ X5 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('2',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t25_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X31 @ X34 ) @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X31 @ X33 ) @ ( k4_tarski @ X34 @ X32 ) @ ( k4_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t25_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_tarski @ ( k4_tarski @ X14 @ X15 ) @ ( k4_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['2','11','12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQLkt4JRaO
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 11.10/11.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.10/11.33  % Solved by: fo/fo7.sh
% 11.10/11.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.10/11.33  % done 9815 iterations in 10.909s
% 11.10/11.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.10/11.33  % SZS output start Refutation
% 11.10/11.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.10/11.33  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.10/11.33  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 11.10/11.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.10/11.33  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.10/11.33  thf(sk_C_type, type, sk_C: $i).
% 11.10/11.33  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 11.10/11.33  thf(sk_B_type, type, sk_B: $i).
% 11.10/11.33  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 11.10/11.33  thf(sk_D_type, type, sk_D: $i).
% 11.10/11.33  thf(sk_E_type, type, sk_E: $i).
% 11.10/11.33  thf(sk_A_type, type, sk_A: $i).
% 11.10/11.33  thf(t45_mcart_1, conjecture,
% 11.10/11.33    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 11.10/11.33     ( ( k3_zfmisc_1 @
% 11.10/11.33         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 11.10/11.33       ( k2_enumset1 @
% 11.10/11.33         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 11.10/11.33         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 11.10/11.33  thf(zf_stmt_0, negated_conjecture,
% 11.10/11.33    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 11.10/11.33        ( ( k3_zfmisc_1 @
% 11.10/11.33            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 11.10/11.33          ( k2_enumset1 @
% 11.10/11.33            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 11.10/11.33            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 11.10/11.33    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 11.10/11.33  thf('0', plain,
% 11.10/11.33      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 11.10/11.33         (k2_tarski @ sk_D @ sk_E))
% 11.10/11.33         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 11.10/11.33             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 11.10/11.33             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 11.10/11.33             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 11.10/11.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.10/11.33  thf(t104_enumset1, axiom,
% 11.10/11.33    (![A:$i,B:$i,C:$i,D:$i]:
% 11.10/11.33     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 11.10/11.33  thf('1', plain,
% 11.10/11.33      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 11.10/11.33         ((k2_enumset1 @ X4 @ X6 @ X5 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 11.10/11.33      inference('cnf', [status(esa)], [t104_enumset1])).
% 11.10/11.33  thf('2', plain,
% 11.10/11.33      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 11.10/11.33         (k2_tarski @ sk_D @ sk_E))
% 11.10/11.33         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 11.10/11.33             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 11.10/11.33             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 11.10/11.33             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 11.10/11.33      inference('demod', [status(thm)], ['0', '1'])).
% 11.10/11.33  thf(d3_mcart_1, axiom,
% 11.10/11.33    (![A:$i,B:$i,C:$i]:
% 11.10/11.33     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 11.10/11.33  thf('3', plain,
% 11.10/11.33      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.10/11.33         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 11.10/11.33           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 11.10/11.33      inference('cnf', [status(esa)], [d3_mcart_1])).
% 11.10/11.33  thf('4', plain,
% 11.10/11.33      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.10/11.33         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 11.10/11.33           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 11.10/11.33      inference('cnf', [status(esa)], [d3_mcart_1])).
% 11.10/11.33  thf(t25_mcart_1, axiom,
% 11.10/11.33    (![A:$i,B:$i,C:$i,D:$i]:
% 11.10/11.33     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 11.10/11.33       ( k2_enumset1 @
% 11.10/11.33         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 11.10/11.33         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 11.10/11.33  thf('5', plain,
% 11.10/11.33      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 11.10/11.33         ((k2_zfmisc_1 @ (k2_tarski @ X31 @ X34) @ (k2_tarski @ X32 @ X33))
% 11.10/11.33           = (k2_enumset1 @ (k4_tarski @ X31 @ X32) @ 
% 11.10/11.33              (k4_tarski @ X31 @ X33) @ (k4_tarski @ X34 @ X32) @ 
% 11.10/11.33              (k4_tarski @ X34 @ X33)))),
% 11.10/11.33      inference('cnf', [status(esa)], [t25_mcart_1])).
% 11.10/11.33  thf('6', plain,
% 11.10/11.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.10/11.33         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 11.10/11.33           (k2_tarski @ X0 @ X3))
% 11.10/11.33           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 11.10/11.33              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 11.10/11.33              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 11.10/11.33      inference('sup+', [status(thm)], ['4', '5'])).
% 11.10/11.33  thf('7', plain,
% 11.10/11.33      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.10/11.33         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 11.10/11.33           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 11.10/11.33      inference('cnf', [status(esa)], [d3_mcart_1])).
% 11.10/11.33  thf('8', plain,
% 11.10/11.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.10/11.33         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 11.10/11.33           (k2_tarski @ X0 @ X3))
% 11.10/11.33           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 11.10/11.33              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 11.10/11.33              (k4_tarski @ X4 @ X3)))),
% 11.10/11.33      inference('demod', [status(thm)], ['6', '7'])).
% 11.10/11.33  thf('9', plain,
% 11.10/11.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 11.10/11.33         ((k2_zfmisc_1 @ 
% 11.10/11.33           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 11.10/11.33           (k2_tarski @ X0 @ X3))
% 11.10/11.33           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 11.10/11.33              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 11.10/11.33              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 11.10/11.33      inference('sup+', [status(thm)], ['3', '8'])).
% 11.10/11.33  thf('10', plain,
% 11.10/11.33      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.10/11.33         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 11.10/11.33           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 11.10/11.33      inference('cnf', [status(esa)], [d3_mcart_1])).
% 11.10/11.33  thf('11', plain,
% 11.10/11.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 11.10/11.33         ((k2_zfmisc_1 @ 
% 11.10/11.33           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 11.10/11.33           (k2_tarski @ X0 @ X3))
% 11.10/11.33           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 11.10/11.33              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 11.10/11.33              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 11.10/11.33      inference('demod', [status(thm)], ['9', '10'])).
% 11.10/11.33  thf(t36_zfmisc_1, axiom,
% 11.10/11.33    (![A:$i,B:$i,C:$i]:
% 11.10/11.33     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 11.10/11.33         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 11.10/11.33       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 11.10/11.33         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 11.10/11.33  thf('12', plain,
% 11.10/11.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.10/11.33         ((k2_zfmisc_1 @ (k1_tarski @ X14) @ (k2_tarski @ X15 @ X16))
% 11.10/11.33           = (k2_tarski @ (k4_tarski @ X14 @ X15) @ (k4_tarski @ X14 @ X16)))),
% 11.10/11.33      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 11.10/11.33  thf(d3_zfmisc_1, axiom,
% 11.10/11.33    (![A:$i,B:$i,C:$i]:
% 11.10/11.33     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 11.10/11.33       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 11.10/11.33  thf('13', plain,
% 11.10/11.33      (![X28 : $i, X29 : $i, X30 : $i]:
% 11.10/11.33         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 11.10/11.33           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 11.10/11.33      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.10/11.33  thf('14', plain,
% 11.10/11.33      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 11.10/11.33         (k2_tarski @ sk_D @ sk_E))
% 11.10/11.33         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 11.10/11.33             (k2_tarski @ sk_D @ sk_E)))),
% 11.10/11.33      inference('demod', [status(thm)], ['2', '11', '12', '13'])).
% 11.10/11.33  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 11.10/11.33  
% 11.10/11.33  % SZS output end Refutation
% 11.10/11.33  
% 11.10/11.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
