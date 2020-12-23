%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t9Z2dEqkw7

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Timeout 58.07s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  448 ( 765 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k5_relat_1 @ X20 @ X19 ) @ ( k5_relat_1 @ X20 @ X18 ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k5_relat_1 @ X20 @ X19 ) @ ( k5_relat_1 @ X20 @ X18 ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32','33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t9Z2dEqkw7
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 58.07/58.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 58.07/58.32  % Solved by: fo/fo7.sh
% 58.07/58.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.07/58.32  % done 18921 iterations in 57.831s
% 58.07/58.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 58.07/58.32  % SZS output start Refutation
% 58.07/58.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 58.07/58.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 58.07/58.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 58.07/58.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 58.07/58.32  thf(sk_C_type, type, sk_C: $i).
% 58.07/58.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 58.07/58.32  thf(sk_A_type, type, sk_A: $i).
% 58.07/58.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 58.07/58.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 58.07/58.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 58.07/58.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 58.07/58.32  thf(sk_B_type, type, sk_B: $i).
% 58.07/58.32  thf(commutativity_k2_tarski, axiom,
% 58.07/58.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 58.07/58.32  thf('0', plain,
% 58.07/58.32      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 58.07/58.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 58.07/58.32  thf(t12_setfam_1, axiom,
% 58.07/58.32    (![A:$i,B:$i]:
% 58.07/58.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 58.07/58.32  thf('1', plain,
% 58.07/58.32      (![X11 : $i, X12 : $i]:
% 58.07/58.32         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 58.07/58.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 58.07/58.32  thf('2', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]:
% 58.07/58.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 58.07/58.32      inference('sup+', [status(thm)], ['0', '1'])).
% 58.07/58.32  thf('3', plain,
% 58.07/58.32      (![X11 : $i, X12 : $i]:
% 58.07/58.32         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 58.07/58.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 58.07/58.32  thf('4', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 58.07/58.32      inference('sup+', [status(thm)], ['2', '3'])).
% 58.07/58.32  thf(t48_xboole_1, axiom,
% 58.07/58.32    (![A:$i,B:$i]:
% 58.07/58.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 58.07/58.32  thf('5', plain,
% 58.07/58.32      (![X5 : $i, X6 : $i]:
% 58.07/58.32         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 58.07/58.32           = (k3_xboole_0 @ X5 @ X6))),
% 58.07/58.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 58.07/58.32  thf(t36_xboole_1, axiom,
% 58.07/58.32    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 58.07/58.32  thf('6', plain,
% 58.07/58.32      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 58.07/58.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 58.07/58.32  thf('7', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 58.07/58.32      inference('sup+', [status(thm)], ['5', '6'])).
% 58.07/58.32  thf(t3_subset, axiom,
% 58.07/58.32    (![A:$i,B:$i]:
% 58.07/58.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 58.07/58.32  thf('8', plain,
% 58.07/58.32      (![X13 : $i, X15 : $i]:
% 58.07/58.32         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 58.07/58.32      inference('cnf', [status(esa)], [t3_subset])).
% 58.07/58.32  thf('9', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]:
% 58.07/58.32         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 58.07/58.32      inference('sup-', [status(thm)], ['7', '8'])).
% 58.07/58.32  thf(cc2_relat_1, axiom,
% 58.07/58.32    (![A:$i]:
% 58.07/58.32     ( ( v1_relat_1 @ A ) =>
% 58.07/58.32       ( ![B:$i]:
% 58.07/58.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 58.07/58.32  thf('10', plain,
% 58.07/58.32      (![X16 : $i, X17 : $i]:
% 58.07/58.32         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 58.07/58.32          | (v1_relat_1 @ X16)
% 58.07/58.32          | ~ (v1_relat_1 @ X17))),
% 58.07/58.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 58.07/58.32  thf('11', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 58.07/58.32      inference('sup-', [status(thm)], ['9', '10'])).
% 58.07/58.32  thf('12', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]:
% 58.07/58.32         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 58.07/58.32      inference('sup+', [status(thm)], ['4', '11'])).
% 58.07/58.32  thf('13', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 58.07/58.32      inference('sup+', [status(thm)], ['2', '3'])).
% 58.07/58.32  thf('14', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 58.07/58.32      inference('sup+', [status(thm)], ['5', '6'])).
% 58.07/58.32  thf('15', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 58.07/58.32      inference('sup+', [status(thm)], ['13', '14'])).
% 58.07/58.32  thf(t48_relat_1, axiom,
% 58.07/58.32    (![A:$i]:
% 58.07/58.32     ( ( v1_relat_1 @ A ) =>
% 58.07/58.32       ( ![B:$i]:
% 58.07/58.32         ( ( v1_relat_1 @ B ) =>
% 58.07/58.32           ( ![C:$i]:
% 58.07/58.32             ( ( v1_relat_1 @ C ) =>
% 58.07/58.32               ( ( r1_tarski @ A @ B ) =>
% 58.07/58.32                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 58.07/58.32  thf('16', plain,
% 58.07/58.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X18)
% 58.07/58.32          | ~ (r1_tarski @ X19 @ X18)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X20 @ X19) @ (k5_relat_1 @ X20 @ X18))
% 58.07/58.32          | ~ (v1_relat_1 @ X20)
% 58.07/58.32          | ~ (v1_relat_1 @ X19))),
% 58.07/58.32      inference('cnf', [status(esa)], [t48_relat_1])).
% 58.07/58.32  thf('17', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 58.07/58.32          | ~ (v1_relat_1 @ X2)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.07/58.32             (k5_relat_1 @ X2 @ X0))
% 58.07/58.32          | ~ (v1_relat_1 @ X0))),
% 58.07/58.32      inference('sup-', [status(thm)], ['15', '16'])).
% 58.07/58.32  thf('18', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X0)
% 58.07/58.32          | ~ (v1_relat_1 @ X0)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.07/58.32             (k5_relat_1 @ X2 @ X0))
% 58.07/58.32          | ~ (v1_relat_1 @ X2))),
% 58.07/58.32      inference('sup-', [status(thm)], ['12', '17'])).
% 58.07/58.32  thf('19', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X2)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.07/58.32             (k5_relat_1 @ X2 @ X0))
% 58.07/58.32          | ~ (v1_relat_1 @ X0))),
% 58.07/58.32      inference('simplify', [status(thm)], ['18'])).
% 58.07/58.32  thf('20', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 58.07/58.32      inference('sup-', [status(thm)], ['9', '10'])).
% 58.07/58.32  thf('21', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 58.07/58.32      inference('sup+', [status(thm)], ['5', '6'])).
% 58.07/58.32  thf('22', plain,
% 58.07/58.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X18)
% 58.07/58.32          | ~ (r1_tarski @ X19 @ X18)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X20 @ X19) @ (k5_relat_1 @ X20 @ X18))
% 58.07/58.32          | ~ (v1_relat_1 @ X20)
% 58.07/58.32          | ~ (v1_relat_1 @ X19))),
% 58.07/58.32      inference('cnf', [status(esa)], [t48_relat_1])).
% 58.07/58.32  thf('23', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 58.07/58.32          | ~ (v1_relat_1 @ X2)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 58.07/58.32             (k5_relat_1 @ X2 @ X0))
% 58.07/58.32          | ~ (v1_relat_1 @ X0))),
% 58.07/58.32      inference('sup-', [status(thm)], ['21', '22'])).
% 58.07/58.32  thf('24', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X1)
% 58.07/58.32          | ~ (v1_relat_1 @ X1)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.07/58.32             (k5_relat_1 @ X2 @ X1))
% 58.07/58.32          | ~ (v1_relat_1 @ X2))),
% 58.07/58.32      inference('sup-', [status(thm)], ['20', '23'])).
% 58.07/58.32  thf('25', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X2)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.07/58.32             (k5_relat_1 @ X2 @ X1))
% 58.07/58.32          | ~ (v1_relat_1 @ X1))),
% 58.07/58.32      inference('simplify', [status(thm)], ['24'])).
% 58.07/58.32  thf(t19_xboole_1, axiom,
% 58.07/58.32    (![A:$i,B:$i,C:$i]:
% 58.07/58.32     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 58.07/58.32       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 58.07/58.32  thf('26', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (r1_tarski @ X0 @ X1)
% 58.07/58.32          | ~ (r1_tarski @ X0 @ X2)
% 58.07/58.32          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 58.07/58.32      inference('cnf', [status(esa)], [t19_xboole_1])).
% 58.07/58.32  thf('27', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X0)
% 58.07/58.32          | ~ (v1_relat_1 @ X1)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 58.07/58.32             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 58.07/58.32          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 58.07/58.32      inference('sup-', [status(thm)], ['25', '26'])).
% 58.07/58.32  thf('28', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X0)
% 58.07/58.32          | ~ (v1_relat_1 @ X1)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 58.07/58.32             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 58.07/58.32          | ~ (v1_relat_1 @ X1)
% 58.07/58.32          | ~ (v1_relat_1 @ X2))),
% 58.07/58.32      inference('sup-', [status(thm)], ['19', '27'])).
% 58.07/58.32  thf('29', plain,
% 58.07/58.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.07/58.32         (~ (v1_relat_1 @ X2)
% 58.07/58.32          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 58.07/58.32             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 58.07/58.32          | ~ (v1_relat_1 @ X1)
% 58.07/58.32          | ~ (v1_relat_1 @ X0))),
% 58.07/58.32      inference('simplify', [status(thm)], ['28'])).
% 58.07/58.32  thf(t52_relat_1, conjecture,
% 58.07/58.32    (![A:$i]:
% 58.07/58.32     ( ( v1_relat_1 @ A ) =>
% 58.07/58.32       ( ![B:$i]:
% 58.07/58.32         ( ( v1_relat_1 @ B ) =>
% 58.07/58.32           ( ![C:$i]:
% 58.07/58.32             ( ( v1_relat_1 @ C ) =>
% 58.07/58.32               ( r1_tarski @
% 58.07/58.32                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 58.07/58.32                 ( k3_xboole_0 @
% 58.07/58.32                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 58.07/58.32  thf(zf_stmt_0, negated_conjecture,
% 58.07/58.32    (~( ![A:$i]:
% 58.07/58.32        ( ( v1_relat_1 @ A ) =>
% 58.07/58.32          ( ![B:$i]:
% 58.07/58.32            ( ( v1_relat_1 @ B ) =>
% 58.07/58.32              ( ![C:$i]:
% 58.07/58.32                ( ( v1_relat_1 @ C ) =>
% 58.07/58.32                  ( r1_tarski @
% 58.07/58.32                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 58.07/58.32                    ( k3_xboole_0 @
% 58.07/58.32                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 58.07/58.32    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 58.07/58.32  thf('30', plain,
% 58.07/58.32      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 58.07/58.32          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 58.07/58.32           (k5_relat_1 @ sk_A @ sk_C)))),
% 58.07/58.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.07/58.32  thf('31', plain,
% 58.07/58.32      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 58.07/58.32      inference('sup-', [status(thm)], ['29', '30'])).
% 58.07/58.32  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 58.07/58.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.07/58.32  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 58.07/58.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.07/58.32  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 58.07/58.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.07/58.32  thf('35', plain, ($false),
% 58.07/58.32      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 58.07/58.32  
% 58.07/58.32  % SZS output end Refutation
% 58.07/58.32  
% 58.07/58.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
