%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dsp1EMOOO4

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:13 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  426 ( 574 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf(t51_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ A @ ( k2_xboole_0 @ B @ C ) )
                = ( k2_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) )
        = ( k2_xboole_0 @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t51_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ X0 ) @ ( k5_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) )
        = ( k2_xboole_0 @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t51_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k5_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k5_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k5_relat_1 @ X2 @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k5_relat_1 @ X2 @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k5_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k5_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t53_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k6_subset_1 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) @ ( k5_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k6_subset_1 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) @ ( k5_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_relat_1])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) @ ( k5_relat_1 @ sk_A @ ( k6_subset_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) @ ( k5_relat_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dsp1EMOOO4
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 435 iterations in 0.605s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.84/1.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.05  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.84/1.05  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.05  thf(fc2_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.84/1.05  thf('0', plain,
% 0.84/1.05      (![X13 : $i, X14 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.84/1.05  thf(t51_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( v1_relat_1 @ B ) =>
% 0.84/1.05           ( ![C:$i]:
% 0.84/1.05             ( ( v1_relat_1 @ C ) =>
% 0.84/1.05               ( ( k5_relat_1 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.84/1.05                 ( k2_xboole_0 @
% 0.84/1.05                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf('1', plain,
% 0.84/1.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X15)
% 0.84/1.05          | ((k5_relat_1 @ X16 @ (k2_xboole_0 @ X15 @ X17))
% 0.84/1.05              = (k2_xboole_0 @ (k5_relat_1 @ X16 @ X15) @ 
% 0.84/1.05                 (k5_relat_1 @ X16 @ X17)))
% 0.84/1.05          | ~ (v1_relat_1 @ X17)
% 0.84/1.05          | ~ (v1_relat_1 @ X16))),
% 0.84/1.05      inference('cnf', [status(esa)], [t51_relat_1])).
% 0.84/1.05  thf(commutativity_k2_tarski, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.05  thf(l51_zfmisc_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('3', plain,
% 0.84/1.05      (![X9 : $i, X10 : $i]:
% 0.84/1.05         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['2', '3'])).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X9 : $i, X10 : $i]:
% 0.84/1.05         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['4', '5'])).
% 0.84/1.05  thf(t7_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.05  thf('8', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['6', '7'])).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r1_tarski @ (k5_relat_1 @ X2 @ X0) @ 
% 0.84/1.05           (k5_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['1', '8'])).
% 0.84/1.05  thf(t39_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.84/1.05           = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X15)
% 0.84/1.05          | ((k5_relat_1 @ X16 @ (k2_xboole_0 @ X15 @ X17))
% 0.84/1.05              = (k2_xboole_0 @ (k5_relat_1 @ X16 @ X15) @ 
% 0.84/1.05                 (k5_relat_1 @ X16 @ X17)))
% 0.84/1.05          | ~ (v1_relat_1 @ X17)
% 0.84/1.05          | ~ (v1_relat_1 @ X16))),
% 0.84/1.05      inference('cnf', [status(esa)], [t51_relat_1])).
% 0.84/1.05  thf(t43_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.84/1.05       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.05         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 0.84/1.05          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.84/1.05  thf('13', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X3 @ (k5_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.84/1.05             (k5_relat_1 @ X2 @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X3 @ (k5_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.84/1.05          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.84/1.05             (k5_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.84/1.05          | ~ (v1_relat_1 @ X2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['10', '13'])).
% 0.84/1.05  thf('15', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | (r1_tarski @ 
% 0.84/1.05             (k4_xboole_0 @ (k5_relat_1 @ X2 @ X0) @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.84/1.05             (k5_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['9', '14'])).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r1_tarski @ 
% 0.84/1.05           (k4_xboole_0 @ (k5_relat_1 @ X2 @ X0) @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.84/1.05           (k5_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.84/1.05          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('simplify', [status(thm)], ['15'])).
% 0.84/1.05  thf('17', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | (r1_tarski @ 
% 0.84/1.05             (k4_xboole_0 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X2 @ X0)) @ 
% 0.84/1.05             (k5_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['0', '16'])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r1_tarski @ 
% 0.84/1.05           (k4_xboole_0 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X2 @ X0)) @ 
% 0.84/1.05           (k5_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ X2)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('simplify', [status(thm)], ['17'])).
% 0.84/1.05  thf(t53_relat_1, conjecture,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( v1_relat_1 @ B ) =>
% 0.84/1.05           ( ![C:$i]:
% 0.84/1.05             ( ( v1_relat_1 @ C ) =>
% 0.84/1.05               ( r1_tarski @
% 0.84/1.05                 ( k6_subset_1 @
% 0.84/1.05                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) @ 
% 0.84/1.05                 ( k5_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i]:
% 0.84/1.05        ( ( v1_relat_1 @ A ) =>
% 0.84/1.05          ( ![B:$i]:
% 0.84/1.05            ( ( v1_relat_1 @ B ) =>
% 0.84/1.05              ( ![C:$i]:
% 0.84/1.05                ( ( v1_relat_1 @ C ) =>
% 0.84/1.05                  ( r1_tarski @
% 0.84/1.05                    ( k6_subset_1 @
% 0.84/1.05                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) @ 
% 0.84/1.05                    ( k5_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t53_relat_1])).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      (~ (r1_tarski @ 
% 0.84/1.05          (k6_subset_1 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 0.84/1.05           (k5_relat_1 @ sk_A @ sk_C)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_A @ (k6_subset_1 @ sk_B @ sk_C)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(redefinition_k6_subset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('20', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i]:
% 0.84/1.05         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i]:
% 0.84/1.05         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      (~ (r1_tarski @ 
% 0.84/1.05          (k4_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 0.84/1.05           (k5_relat_1 @ sk_A @ sk_C)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.84/1.05      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['18', '22'])).
% 0.84/1.05  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('27', plain, ($false),
% 0.84/1.05      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
