%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YYBTm9Iuu

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  339 ( 433 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_xboole_0 @ X4 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X15 @ ( k7_relat_1 @ X15 @ X16 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X15 @ ( k7_relat_1 @ X15 @ X16 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k7_relat_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YYBTm9Iuu
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 15:46:59 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 38 iterations in 0.025s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t216_relat_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.21/0.52           ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ C ) =>
% 0.21/0.52          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.21/0.52              ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.21/0.52  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t85_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.52          | (r1_xboole_0 @ X4 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf(commutativity_k2_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.52  thf(t12_setfam_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '11'])).
% 0.21/0.52  thf(t212_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.21/0.52         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k6_subset_1 @ X15 @ (k7_relat_1 @ X15 @ X16)))
% 0.21/0.52            = (k6_subset_1 @ (k1_relat_1 @ X15) @ X16))
% 0.21/0.52          | ~ (v1_relat_1 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.21/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k4_xboole_0 @ X15 @ (k7_relat_1 @ X15 @ X16)))
% 0.21/0.52            = (k4_xboole_0 @ (k1_relat_1 @ X15) @ X16))
% 0.21/0.52          | ~ (v1_relat_1 @ X15))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.52  thf(t95_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ (k1_relat_1 @ X17) @ X18)
% 0.21/0.52          | ((k7_relat_1 @ X17 @ X18) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.52          | ((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.21/0.52              = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.21/0.52            = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '18'])).
% 0.21/0.52  thf(fc2_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.21/0.52              = (k1_xboole_0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((k7_relat_1 @ (k6_subset_1 @ sk_C_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.21/0.52         sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((k7_relat_1 @ (k4_xboole_0 @ sk_C_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.21/0.52         sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.52  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
