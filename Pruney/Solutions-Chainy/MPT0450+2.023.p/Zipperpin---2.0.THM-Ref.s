%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MAE3rypkhp

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:04 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  340 ( 606 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_D @ X12 @ X13 ) ) @ X13 )
      | ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_D @ X12 @ X13 ) ) @ X12 )
      | ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k3_relat_1 @ X20 ) @ ( k3_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MAE3rypkhp
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.20  % Solved by: fo/fo7.sh
% 1.97/2.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.20  % done 1914 iterations in 1.756s
% 1.97/2.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.20  % SZS output start Refutation
% 1.97/2.20  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.97/2.20  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.97/2.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.97/2.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.97/2.20  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.20  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.97/2.20  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.97/2.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.97/2.20  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.97/2.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.97/2.20  thf(commutativity_k2_tarski, axiom,
% 1.97/2.20    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.97/2.20  thf('0', plain,
% 1.97/2.20      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 1.97/2.20      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.97/2.20  thf(t12_setfam_1, axiom,
% 1.97/2.20    (![A:$i,B:$i]:
% 1.97/2.20     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.97/2.20  thf('1', plain,
% 1.97/2.20      (![X10 : $i, X11 : $i]:
% 1.97/2.20         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 1.97/2.20      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.20  thf('2', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.97/2.20      inference('sup+', [status(thm)], ['0', '1'])).
% 1.97/2.20  thf('3', plain,
% 1.97/2.20      (![X10 : $i, X11 : $i]:
% 1.97/2.20         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 1.97/2.20      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.20  thf('4', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.97/2.20      inference('sup+', [status(thm)], ['2', '3'])).
% 1.97/2.20  thf(fc1_relat_1, axiom,
% 1.97/2.20    (![A:$i,B:$i]:
% 1.97/2.20     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.97/2.20  thf('5', plain,
% 1.97/2.20      (![X17 : $i, X18 : $i]:
% 1.97/2.20         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.97/2.20      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.97/2.20  thf(d3_relat_1, axiom,
% 1.97/2.20    (![A:$i]:
% 1.97/2.20     ( ( v1_relat_1 @ A ) =>
% 1.97/2.20       ( ![B:$i]:
% 1.97/2.20         ( ( r1_tarski @ A @ B ) <=>
% 1.97/2.20           ( ![C:$i,D:$i]:
% 1.97/2.20             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 1.97/2.20               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 1.97/2.20  thf('6', plain,
% 1.97/2.20      (![X12 : $i, X13 : $i]:
% 1.97/2.20         ((r2_hidden @ (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_D @ X12 @ X13)) @ 
% 1.97/2.20           X13)
% 1.97/2.20          | (r1_tarski @ X13 @ X12)
% 1.97/2.20          | ~ (v1_relat_1 @ X13))),
% 1.97/2.20      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.97/2.20  thf('7', plain,
% 1.97/2.20      (![X12 : $i, X13 : $i]:
% 1.97/2.20         (~ (r2_hidden @ 
% 1.97/2.20             (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_D @ X12 @ X13)) @ X12)
% 1.97/2.20          | (r1_tarski @ X13 @ X12)
% 1.97/2.20          | ~ (v1_relat_1 @ X13))),
% 1.97/2.20      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.97/2.20  thf('8', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         (~ (v1_relat_1 @ X0)
% 1.97/2.20          | (r1_tarski @ X0 @ X0)
% 1.97/2.20          | ~ (v1_relat_1 @ X0)
% 1.97/2.20          | (r1_tarski @ X0 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.20  thf('9', plain, (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ~ (v1_relat_1 @ X0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['8'])).
% 1.97/2.20  thf(t18_xboole_1, axiom,
% 1.97/2.20    (![A:$i,B:$i,C:$i]:
% 1.97/2.20     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.97/2.20  thf('10', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.20         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.97/2.20      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.97/2.20  thf('11', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.97/2.20          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.97/2.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.97/2.20  thf('12', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.97/2.20      inference('sup-', [status(thm)], ['5', '11'])).
% 1.97/2.20  thf(t31_relat_1, axiom,
% 1.97/2.20    (![A:$i]:
% 1.97/2.20     ( ( v1_relat_1 @ A ) =>
% 1.97/2.20       ( ![B:$i]:
% 1.97/2.20         ( ( v1_relat_1 @ B ) =>
% 1.97/2.21           ( ( r1_tarski @ A @ B ) =>
% 1.97/2.21             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.97/2.21  thf('13', plain,
% 1.97/2.21      (![X19 : $i, X20 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X19)
% 1.97/2.21          | (r1_tarski @ (k3_relat_1 @ X20) @ (k3_relat_1 @ X19))
% 1.97/2.21          | ~ (r1_tarski @ X20 @ X19)
% 1.97/2.21          | ~ (v1_relat_1 @ X20))),
% 1.97/2.21      inference('cnf', [status(esa)], [t31_relat_1])).
% 1.97/2.21  thf('14', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X0)
% 1.97/2.21          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.97/2.21          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.97/2.21             (k3_relat_1 @ X0))
% 1.97/2.21          | ~ (v1_relat_1 @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['12', '13'])).
% 1.97/2.21  thf('15', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]:
% 1.97/2.21         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.97/2.21           (k3_relat_1 @ X0))
% 1.97/2.21          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.97/2.21          | ~ (v1_relat_1 @ X0))),
% 1.97/2.21      inference('simplify', [status(thm)], ['14'])).
% 1.97/2.21  thf('16', plain,
% 1.97/2.21      (![X17 : $i, X18 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.97/2.21      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.97/2.21  thf('17', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X0)
% 1.97/2.21          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.97/2.21             (k3_relat_1 @ X0)))),
% 1.97/2.21      inference('clc', [status(thm)], ['15', '16'])).
% 1.97/2.21  thf('18', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]:
% 1.97/2.21         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.97/2.21           (k3_relat_1 @ X0))
% 1.97/2.21          | ~ (v1_relat_1 @ X0))),
% 1.97/2.21      inference('sup+', [status(thm)], ['4', '17'])).
% 1.97/2.21  thf('19', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X0)
% 1.97/2.21          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.97/2.21             (k3_relat_1 @ X0)))),
% 1.97/2.21      inference('clc', [status(thm)], ['15', '16'])).
% 1.97/2.21  thf(t19_xboole_1, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i]:
% 1.97/2.21     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.97/2.21       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.97/2.21  thf('20', plain,
% 1.97/2.21      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.97/2.21         (~ (r1_tarski @ X3 @ X4)
% 1.97/2.21          | ~ (r1_tarski @ X3 @ X5)
% 1.97/2.21          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.97/2.21      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.97/2.21  thf('21', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X0)
% 1.97/2.21          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.97/2.21             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 1.97/2.21          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 1.97/2.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.97/2.21  thf('22', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]:
% 1.97/2.21         (~ (v1_relat_1 @ X0)
% 1.97/2.21          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.97/2.21             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 1.97/2.21          | ~ (v1_relat_1 @ X1))),
% 1.97/2.21      inference('sup-', [status(thm)], ['18', '21'])).
% 1.97/2.21  thf(t34_relat_1, conjecture,
% 1.97/2.21    (![A:$i]:
% 1.97/2.21     ( ( v1_relat_1 @ A ) =>
% 1.97/2.21       ( ![B:$i]:
% 1.97/2.21         ( ( v1_relat_1 @ B ) =>
% 1.97/2.21           ( r1_tarski @
% 1.97/2.21             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.97/2.21             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.97/2.21  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.21    (~( ![A:$i]:
% 1.97/2.21        ( ( v1_relat_1 @ A ) =>
% 1.97/2.21          ( ![B:$i]:
% 1.97/2.21            ( ( v1_relat_1 @ B ) =>
% 1.97/2.21              ( r1_tarski @
% 1.97/2.21                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.97/2.21                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.97/2.21    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 1.97/2.21  thf('23', plain,
% 1.97/2.21      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.97/2.21          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('24', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.97/2.21      inference('sup-', [status(thm)], ['22', '23'])).
% 1.97/2.21  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('27', plain, ($false),
% 1.97/2.21      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.97/2.21  
% 1.97/2.21  % SZS output end Refutation
% 1.97/2.21  
% 1.97/2.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
