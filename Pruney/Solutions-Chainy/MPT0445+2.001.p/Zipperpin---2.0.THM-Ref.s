%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A50N7h3JTM

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:50 EST 2020

% Result     : Theorem 2.57s
% Output     : Refutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  405 ( 571 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X23 @ X22 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X23 @ X22 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t28_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_relat_1])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A50N7h3JTM
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:40:55 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 2.57/2.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.57/2.78  % Solved by: fo/fo7.sh
% 2.57/2.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.57/2.78  % done 2712 iterations in 2.297s
% 2.57/2.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.57/2.78  % SZS output start Refutation
% 2.57/2.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.57/2.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.57/2.78  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.57/2.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.57/2.78  thf(sk_A_type, type, sk_A: $i).
% 2.57/2.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.57/2.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.57/2.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.57/2.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.57/2.78  thf(sk_B_type, type, sk_B: $i).
% 2.57/2.78  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.57/2.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.57/2.78  thf(commutativity_k2_tarski, axiom,
% 2.57/2.78    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.57/2.78  thf('0', plain,
% 2.57/2.78      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 2.57/2.78      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.57/2.78  thf(l51_zfmisc_1, axiom,
% 2.57/2.78    (![A:$i,B:$i]:
% 2.57/2.78     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.57/2.78  thf('1', plain,
% 2.57/2.78      (![X9 : $i, X10 : $i]:
% 2.57/2.78         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 2.57/2.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.57/2.78  thf('2', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.57/2.78      inference('sup+', [status(thm)], ['0', '1'])).
% 2.57/2.78  thf('3', plain,
% 2.57/2.78      (![X9 : $i, X10 : $i]:
% 2.57/2.78         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 2.57/2.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.57/2.78  thf('4', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.57/2.78      inference('sup+', [status(thm)], ['2', '3'])).
% 2.57/2.78  thf(t7_xboole_1, axiom,
% 2.57/2.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.57/2.78  thf('5', plain,
% 2.57/2.78      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 2.57/2.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.57/2.78  thf('6', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.57/2.78      inference('sup+', [status(thm)], ['4', '5'])).
% 2.57/2.78  thf(t43_xboole_1, axiom,
% 2.57/2.78    (![A:$i,B:$i,C:$i]:
% 2.57/2.78     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.57/2.78       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.57/2.78  thf('7', plain,
% 2.57/2.78      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.57/2.78         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 2.57/2.78          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 2.57/2.78      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.57/2.78  thf('8', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 2.57/2.78      inference('sup-', [status(thm)], ['6', '7'])).
% 2.57/2.78  thf(t3_subset, axiom,
% 2.57/2.78    (![A:$i,B:$i]:
% 2.57/2.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.57/2.78  thf('9', plain,
% 2.57/2.78      (![X13 : $i, X15 : $i]:
% 2.57/2.78         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 2.57/2.78      inference('cnf', [status(esa)], [t3_subset])).
% 2.57/2.78  thf('10', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.57/2.78      inference('sup-', [status(thm)], ['8', '9'])).
% 2.57/2.78  thf(cc2_relat_1, axiom,
% 2.57/2.78    (![A:$i]:
% 2.57/2.78     ( ( v1_relat_1 @ A ) =>
% 2.57/2.78       ( ![B:$i]:
% 2.57/2.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.57/2.78  thf('11', plain,
% 2.57/2.78      (![X16 : $i, X17 : $i]:
% 2.57/2.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.57/2.78          | (v1_relat_1 @ X16)
% 2.57/2.78          | ~ (v1_relat_1 @ X17))),
% 2.57/2.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.57/2.78  thf('12', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.57/2.78      inference('sup-', [status(thm)], ['10', '11'])).
% 2.57/2.78  thf(t26_relat_1, axiom,
% 2.57/2.78    (![A:$i]:
% 2.57/2.78     ( ( v1_relat_1 @ A ) =>
% 2.57/2.78       ( ![B:$i]:
% 2.57/2.78         ( ( v1_relat_1 @ B ) =>
% 2.57/2.78           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 2.57/2.78             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 2.57/2.78  thf('13', plain,
% 2.57/2.78      (![X22 : $i, X23 : $i]:
% 2.57/2.78         (~ (v1_relat_1 @ X22)
% 2.57/2.78          | ((k2_relat_1 @ (k2_xboole_0 @ X23 @ X22))
% 2.57/2.78              = (k2_xboole_0 @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22)))
% 2.57/2.78          | ~ (v1_relat_1 @ X23))),
% 2.57/2.78      inference('cnf', [status(esa)], [t26_relat_1])).
% 2.57/2.78  thf('14', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.57/2.78      inference('sup+', [status(thm)], ['4', '5'])).
% 2.57/2.78  thf('15', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.57/2.78           (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.57/2.78          | ~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ X0))),
% 2.57/2.78      inference('sup+', [status(thm)], ['13', '14'])).
% 2.57/2.78  thf(t39_xboole_1, axiom,
% 2.57/2.78    (![A:$i,B:$i]:
% 2.57/2.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.57/2.78  thf('16', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.57/2.78           = (k2_xboole_0 @ X0 @ X1))),
% 2.57/2.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.57/2.78  thf('17', plain,
% 2.57/2.78      (![X22 : $i, X23 : $i]:
% 2.57/2.78         (~ (v1_relat_1 @ X22)
% 2.57/2.78          | ((k2_relat_1 @ (k2_xboole_0 @ X23 @ X22))
% 2.57/2.78              = (k2_xboole_0 @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22)))
% 2.57/2.78          | ~ (v1_relat_1 @ X23))),
% 2.57/2.78      inference('cnf', [status(esa)], [t26_relat_1])).
% 2.57/2.78  thf('18', plain,
% 2.57/2.78      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.57/2.78         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 2.57/2.78          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 2.57/2.78      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.57/2.78  thf('19', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.57/2.78         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.57/2.78          | ~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ X0)
% 2.57/2.78          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 2.57/2.78             (k2_relat_1 @ X0)))),
% 2.57/2.78      inference('sup-', [status(thm)], ['17', '18'])).
% 2.57/2.78  thf('20', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.57/2.78         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.57/2.78          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 2.57/2.78             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 2.57/2.78          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 2.57/2.78          | ~ (v1_relat_1 @ X1))),
% 2.57/2.78      inference('sup-', [status(thm)], ['16', '19'])).
% 2.57/2.78  thf('21', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         (~ (v1_relat_1 @ X0)
% 2.57/2.78          | ~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 2.57/2.78          | (r1_tarski @ 
% 2.57/2.78             (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 2.57/2.78             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1))))),
% 2.57/2.78      inference('sup-', [status(thm)], ['15', '20'])).
% 2.57/2.78  thf('22', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 2.57/2.78           (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 2.57/2.78          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 2.57/2.78          | ~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ X0))),
% 2.57/2.78      inference('simplify', [status(thm)], ['21'])).
% 2.57/2.78  thf('23', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         (~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ X1)
% 2.57/2.78          | ~ (v1_relat_1 @ X0)
% 2.57/2.78          | (r1_tarski @ 
% 2.57/2.78             (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 2.57/2.78             (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.57/2.78      inference('sup-', [status(thm)], ['12', '22'])).
% 2.57/2.78  thf('24', plain,
% 2.57/2.78      (![X0 : $i, X1 : $i]:
% 2.57/2.78         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 2.57/2.78           (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)))
% 2.57/2.78          | ~ (v1_relat_1 @ X0)
% 2.57/2.78          | ~ (v1_relat_1 @ X1))),
% 2.57/2.78      inference('simplify', [status(thm)], ['23'])).
% 2.57/2.78  thf(t28_relat_1, conjecture,
% 2.57/2.78    (![A:$i]:
% 2.57/2.78     ( ( v1_relat_1 @ A ) =>
% 2.57/2.78       ( ![B:$i]:
% 2.57/2.78         ( ( v1_relat_1 @ B ) =>
% 2.57/2.78           ( r1_tarski @
% 2.57/2.78             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 2.57/2.78             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.57/2.78  thf(zf_stmt_0, negated_conjecture,
% 2.57/2.78    (~( ![A:$i]:
% 2.57/2.78        ( ( v1_relat_1 @ A ) =>
% 2.57/2.78          ( ![B:$i]:
% 2.57/2.78            ( ( v1_relat_1 @ B ) =>
% 2.57/2.78              ( r1_tarski @
% 2.57/2.78                ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 2.57/2.78                ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ) )),
% 2.57/2.78    inference('cnf.neg', [status(esa)], [t28_relat_1])).
% 2.57/2.78  thf('25', plain,
% 2.57/2.78      (~ (r1_tarski @ 
% 2.57/2.78          (k6_subset_1 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 2.57/2.78          (k2_relat_1 @ (k6_subset_1 @ sk_A @ sk_B)))),
% 2.57/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.57/2.78  thf(redefinition_k6_subset_1, axiom,
% 2.57/2.78    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.57/2.78  thf('26', plain,
% 2.57/2.78      (![X11 : $i, X12 : $i]:
% 2.57/2.78         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 2.57/2.78      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.57/2.78  thf('27', plain,
% 2.57/2.78      (![X11 : $i, X12 : $i]:
% 2.57/2.78         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 2.57/2.78      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.57/2.78  thf('28', plain,
% 2.57/2.78      (~ (r1_tarski @ 
% 2.57/2.78          (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 2.57/2.78          (k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 2.57/2.78      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.57/2.78  thf('29', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 2.57/2.78      inference('sup-', [status(thm)], ['24', '28'])).
% 2.57/2.78  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 2.57/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.57/2.78  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 2.57/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.57/2.78  thf('32', plain, ($false),
% 2.57/2.78      inference('demod', [status(thm)], ['29', '30', '31'])).
% 2.57/2.78  
% 2.57/2.78  % SZS output end Refutation
% 2.57/2.78  
% 2.57/2.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
