%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i3lGknVppb

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  86 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  447 ( 745 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k1_funct_1 @ X21 @ ( k1_funct_1 @ X22 @ X23 ) ) )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X12
       != ( k6_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ( X14 != X16 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('19',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X16 ) @ ( k6_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X16 ) @ ( k6_relat_1 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_A )
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i3lGknVppb
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 252 iterations in 0.126s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(t38_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.21/0.55         ( ( k1_funct_1 @ C @ A ) =
% 0.21/0.55           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.21/0.55            ( ( k1_funct_1 @ C @ A ) =
% 0.21/0.55              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(commutativity_k2_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.55  thf(t12_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.55  thf(d4_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.55          | (r2_hidden @ X4 @ X1)
% 0.21/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.55  thf('9', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.55  thf(t71_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.55  thf('10', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t23_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.55             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.55               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X21)
% 0.21/0.55          | ~ (v1_funct_1 @ X21)
% 0.21/0.55          | ((k1_funct_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 0.21/0.55              = (k1_funct_1 @ X21 @ (k1_funct_1 @ X22 @ X23)))
% 0.21/0.55          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 0.21/0.55          | ~ (v1_funct_1 @ X22)
% 0.21/0.55          | ~ (v1_relat_1 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.55          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.21/0.55              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.21/0.55          | ~ (v1_funct_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf(fc3_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('13', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('14', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.21/0.55              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.21/0.55          | ~ (v1_funct_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.55  thf('17', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.55  thf(d10_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.55         ( ![C:$i,D:$i]:
% 0.21/0.55           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.55             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.55         (((X12) != (k6_relat_1 @ X13))
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 0.21/0.55          | ((X14) != (X16))
% 0.21/0.55          | ~ (r2_hidden @ X14 @ X13)
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X13 : $i, X16 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k6_relat_1 @ X13))
% 0.21/0.55          | ~ (r2_hidden @ X16 @ X13)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X16 @ X16) @ (k6_relat_1 @ X13)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.55  thf('20', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X13 : $i, X16 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X16 @ X13)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X16 @ X16) @ (k6_relat_1 @ X13)))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ (k6_relat_1 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.55  thf(t8_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.55           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.21/0.55          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.21/0.55          | ~ (v1_funct_1 @ X25)
% 0.21/0.55          | ~ (v1_relat_1 @ X25))),
% 0.21/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.55        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.55        | ((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('26', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('27', plain, (((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.55              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((k1_funct_1 @ sk_C_1 @ sk_A)
% 0.21/0.55         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C_1) @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.55  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
