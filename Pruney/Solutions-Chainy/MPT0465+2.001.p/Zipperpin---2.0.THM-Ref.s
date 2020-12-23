%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rwN3gixuAs

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:13 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  422 ( 569 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t51_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ A @ ( k2_xboole_0 @ B @ C ) )
                = ( k2_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ X21 @ ( k2_xboole_0 @ X20 @ X22 ) )
        = ( k2_xboole_0 @ ( k5_relat_1 @ X21 @ X20 ) @ ( k5_relat_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t51_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
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
    inference('sup+',[status(thm)],['5','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ X21 @ ( k2_xboole_0 @ X20 @ X22 ) )
        = ( k2_xboole_0 @ ( k5_relat_1 @ X21 @ X20 ) @ ( k5_relat_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t51_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
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
    inference('sup-',[status(thm)],['4','16'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rwN3gixuAs
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 527 iterations in 0.656s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.10  thf(dt_k6_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.10  thf('0', plain,
% 0.91/1.10      (![X9 : $i, X10 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k6_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.91/1.10  thf(redefinition_k6_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i]:
% 0.91/1.10         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X9 : $i, X10 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k4_xboole_0 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))),
% 0.91/1.10      inference('demod', [status(thm)], ['0', '1'])).
% 0.91/1.10  thf(cc2_relat_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( v1_relat_1 @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X13 : $i, X14 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.91/1.10          | (v1_relat_1 @ X13)
% 0.91/1.10          | ~ (v1_relat_1 @ X14))),
% 0.91/1.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.10  thf(t51_relat_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( v1_relat_1 @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( v1_relat_1 @ B ) =>
% 0.91/1.10           ( ![C:$i]:
% 0.91/1.10             ( ( v1_relat_1 @ C ) =>
% 0.91/1.10               ( ( k5_relat_1 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.91/1.10                 ( k2_xboole_0 @
% 0.91/1.10                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.10         (~ (v1_relat_1 @ X20)
% 0.91/1.10          | ((k5_relat_1 @ X21 @ (k2_xboole_0 @ X20 @ X22))
% 0.91/1.10              = (k2_xboole_0 @ (k5_relat_1 @ X21 @ X20) @ 
% 0.91/1.10                 (k5_relat_1 @ X21 @ X22)))
% 0.91/1.10          | ~ (v1_relat_1 @ X22)
% 0.91/1.10          | ~ (v1_relat_1 @ X21))),
% 0.91/1.10      inference('cnf', [status(esa)], [t51_relat_1])).
% 0.91/1.10  thf(commutativity_k2_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.10  thf(t7_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['6', '7'])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((r1_tarski @ (k5_relat_1 @ X2 @ X0) @ 
% 0.91/1.10           (k5_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | ~ (v1_relat_1 @ X0)
% 0.91/1.10          | ~ (v1_relat_1 @ X1))),
% 0.91/1.10      inference('sup+', [status(thm)], ['5', '8'])).
% 0.91/1.10  thf(t39_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i]:
% 0.91/1.10         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.91/1.10           = (k2_xboole_0 @ X2 @ X3))),
% 0.91/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.10  thf('11', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.10         (~ (v1_relat_1 @ X20)
% 0.91/1.10          | ((k5_relat_1 @ X21 @ (k2_xboole_0 @ X20 @ X22))
% 0.91/1.10              = (k2_xboole_0 @ (k5_relat_1 @ X21 @ X20) @ 
% 0.91/1.10                 (k5_relat_1 @ X21 @ X22)))
% 0.91/1.10          | ~ (v1_relat_1 @ X22)
% 0.91/1.10          | ~ (v1_relat_1 @ X21))),
% 0.91/1.10      inference('cnf', [status(esa)], [t51_relat_1])).
% 0.91/1.10  thf(t43_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.91/1.10       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.10         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.91/1.10          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.10         (~ (r1_tarski @ X3 @ (k5_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | ~ (v1_relat_1 @ X0)
% 0.91/1.10          | ~ (v1_relat_1 @ X1)
% 0.91/1.10          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.91/1.10             (k5_relat_1 @ X2 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.10         (~ (r1_tarski @ X3 @ (k5_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.91/1.10          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.91/1.10             (k5_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.91/1.10          | ~ (v1_relat_1 @ X1)
% 0.91/1.10          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.91/1.10          | ~ (v1_relat_1 @ X2))),
% 0.91/1.10      inference('sup-', [status(thm)], ['10', '13'])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         (~ (v1_relat_1 @ X1)
% 0.91/1.10          | ~ (v1_relat_1 @ X0)
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.91/1.10          | ~ (v1_relat_1 @ X1)
% 0.91/1.10          | (r1_tarski @ 
% 0.91/1.10             (k4_xboole_0 @ (k5_relat_1 @ X2 @ X0) @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.91/1.10             (k5_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '14'])).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((r1_tarski @ 
% 0.91/1.10           (k4_xboole_0 @ (k5_relat_1 @ X2 @ X0) @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.91/1.10           (k5_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.91/1.10          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | ~ (v1_relat_1 @ X0)
% 0.91/1.10          | ~ (v1_relat_1 @ X1))),
% 0.91/1.10      inference('simplify', [status(thm)], ['15'])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         (~ (v1_relat_1 @ X1)
% 0.91/1.10          | ~ (v1_relat_1 @ X0)
% 0.91/1.10          | ~ (v1_relat_1 @ X1)
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | (r1_tarski @ 
% 0.91/1.10             (k4_xboole_0 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X2 @ X0)) @ 
% 0.91/1.10             (k5_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['4', '16'])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((r1_tarski @ 
% 0.91/1.10           (k4_xboole_0 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X2 @ X0)) @ 
% 0.91/1.10           (k5_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.91/1.10          | ~ (v1_relat_1 @ X2)
% 0.91/1.10          | ~ (v1_relat_1 @ X0)
% 0.91/1.10          | ~ (v1_relat_1 @ X1))),
% 0.91/1.10      inference('simplify', [status(thm)], ['17'])).
% 0.91/1.10  thf(t53_relat_1, conjecture,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( v1_relat_1 @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( v1_relat_1 @ B ) =>
% 0.91/1.10           ( ![C:$i]:
% 0.91/1.10             ( ( v1_relat_1 @ C ) =>
% 0.91/1.10               ( r1_tarski @
% 0.91/1.10                 ( k6_subset_1 @
% 0.91/1.10                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) @ 
% 0.91/1.10                 ( k5_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i]:
% 0.91/1.10        ( ( v1_relat_1 @ A ) =>
% 0.91/1.10          ( ![B:$i]:
% 0.91/1.10            ( ( v1_relat_1 @ B ) =>
% 0.91/1.10              ( ![C:$i]:
% 0.91/1.10                ( ( v1_relat_1 @ C ) =>
% 0.91/1.10                  ( r1_tarski @
% 0.91/1.10                    ( k6_subset_1 @
% 0.91/1.10                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) @ 
% 0.91/1.10                    ( k5_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t53_relat_1])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (~ (r1_tarski @ 
% 0.91/1.10          (k6_subset_1 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 0.91/1.10           (k5_relat_1 @ sk_A @ sk_C)) @ 
% 0.91/1.10          (k5_relat_1 @ sk_A @ (k6_subset_1 @ sk_B @ sk_C)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i]:
% 0.91/1.10         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i]:
% 0.91/1.10         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (~ (r1_tarski @ 
% 0.91/1.10          (k4_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 0.91/1.10           (k5_relat_1 @ sk_A @ sk_C)) @ 
% 0.91/1.10          (k5_relat_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.91/1.10      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['18', '22'])).
% 0.91/1.10  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('27', plain, ($false),
% 0.91/1.10      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
