%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8OJclKCDzd

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  273 ( 485 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t157_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ X3 @ X4 ) @ ( k7_relat_1 @ X2 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k7_relat_1 @ sk_B @ X0 ) @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_B @ X0 ) @ ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8OJclKCDzd
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 22 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t157_relat_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ C ) =>
% 0.21/0.47           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.47             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ B ) =>
% 0.21/0.47          ( ![C:$i]:
% 0.21/0.47            ( ( v1_relat_1 @ C ) =>
% 0.21/0.47              ( ( r1_tarski @ B @ C ) =>
% 0.21/0.47                ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t157_relat_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t148_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.21/0.47          | ~ (v1_relat_1 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.21/0.47          | ~ (v1_relat_1 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.47  thf(dt_k7_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.47  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t105_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ C ) =>
% 0.21/0.47           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.47             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X2)
% 0.21/0.47          | (r1_tarski @ (k7_relat_1 @ X3 @ X4) @ (k7_relat_1 @ X2 @ X4))
% 0.21/0.47          | ~ (r1_tarski @ X3 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ sk_B)
% 0.21/0.47          | (r1_tarski @ (k7_relat_1 @ sk_B @ X0) @ (k7_relat_1 @ sk_C @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r1_tarski @ (k7_relat_1 @ sk_B @ X0) @ (k7_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf(t25_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.47             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.47               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X7)
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 0.21/0.47          | ~ (r1_tarski @ X8 @ X7)
% 0.21/0.47          | ~ (v1_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.21/0.47             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ sk_B)
% 0.21/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.21/0.47             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '12'])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.21/0.47             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ sk_C)
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.21/0.47             (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '15'])).
% 0.21/0.47  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 0.21/0.47          (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 0.21/0.47           (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '18'])).
% 0.21/0.47  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 0.21/0.47          (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k9_relat_1 @ sk_C @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '21'])).
% 0.21/0.47  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
