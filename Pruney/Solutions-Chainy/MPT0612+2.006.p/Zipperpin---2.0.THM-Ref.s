%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KAmPuPDQ9i

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:10 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  338 ( 424 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X14 @ ( k7_relat_1 @ X14 @ X15 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X14 @ ( k7_relat_1 @ X14 @ X15 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( ( k7_relat_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KAmPuPDQ9i
% 0.16/0.37  % Computer   : n007.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:33:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 29 iterations in 0.018s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.24/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(t216_relat_1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ C ) =>
% 0.24/0.51       ( ( r1_tarski @ A @ B ) =>
% 0.24/0.51         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.24/0.51           ( k1_xboole_0 ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.51        ( ( v1_relat_1 @ C ) =>
% 0.24/0.51          ( ( r1_tarski @ A @ B ) =>
% 0.24/0.51            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.24/0.51              ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.24/0.51  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t85_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         (~ (r1_tarski @ X3 @ X4)
% 0.24/0.51          | (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.51  thf(d7_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf(commutativity_k2_tarski, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.24/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.24/0.51  thf(t12_setfam_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i, X2 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.51          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['4', '11'])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.24/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.24/0.51  thf(t212_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ B ) =>
% 0.24/0.51       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.24/0.51         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X14 : $i, X15 : $i]:
% 0.24/0.51         (((k1_relat_1 @ (k6_subset_1 @ X14 @ (k7_relat_1 @ X14 @ X15)))
% 0.24/0.51            = (k6_subset_1 @ (k1_relat_1 @ X14) @ X15))
% 0.24/0.51          | ~ (v1_relat_1 @ X14))),
% 0.24/0.51      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.24/0.51  thf(redefinition_k6_subset_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (![X14 : $i, X15 : $i]:
% 0.24/0.51         (((k1_relat_1 @ (k4_xboole_0 @ X14 @ (k7_relat_1 @ X14 @ X15)))
% 0.24/0.51            = (k4_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.24/0.51          | ~ (v1_relat_1 @ X14))),
% 0.24/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.24/0.51  thf(t95_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ B ) =>
% 0.24/0.51       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.51         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X16 : $i, X17 : $i]:
% 0.24/0.51         (~ (r1_xboole_0 @ (k1_relat_1 @ X16) @ X17)
% 0.24/0.51          | ((k7_relat_1 @ X16 @ X17) = (k1_xboole_0))
% 0.24/0.51          | ~ (v1_relat_1 @ X16))),
% 0.24/0.51      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.24/0.51          | ((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.24/0.51              = (k1_xboole_0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.24/0.51            = (k1_xboole_0))
% 0.24/0.51          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)))
% 0.24/0.51          | ~ (v1_relat_1 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['13', '19'])).
% 0.24/0.51  thf(fc2_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.24/0.51      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X0)
% 0.24/0.51          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.24/0.51              = (k1_xboole_0)))),
% 0.24/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.24/0.51         != (k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('24', plain,
% 0.24/0.51      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.24/0.51  thf('25', plain,
% 0.24/0.51      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.24/0.51         != (k1_xboole_0))),
% 0.24/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.51  thf('26', plain,
% 0.24/0.51      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.24/0.51  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('28', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.24/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.24/0.51  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
