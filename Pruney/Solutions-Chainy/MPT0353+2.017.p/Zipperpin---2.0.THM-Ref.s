%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.utWHuzHXTo

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   63 (  81 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  477 ( 758 expanded)
%              Number of equality atoms :   41 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X4 ) @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','9','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.utWHuzHXTo
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 828 iterations in 0.585s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.82/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.82/1.03  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.82/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.03  thf(t32_subset_1, conjecture,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03       ( ![C:$i]:
% 0.82/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.82/1.03             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i,B:$i]:
% 0.82/1.03        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03          ( ![C:$i]:
% 0.82/1.03            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.82/1.03                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.82/1.03  thf('0', plain,
% 0.82/1.03      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.82/1.03         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(redefinition_k7_subset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.82/1.03          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.82/1.03  thf('3', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.82/1.03  thf('4', plain,
% 0.82/1.03      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.82/1.03         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.82/1.03      inference('demod', [status(thm)], ['0', '3'])).
% 0.82/1.03  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(dt_k3_subset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.82/1.03  thf('6', plain,
% 0.82/1.03      (![X11 : $i, X12 : $i]:
% 0.82/1.03         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.82/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.82/1.03      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.82/1.03  thf('7', plain,
% 0.82/1.03      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.82/1.03  thf(redefinition_k9_subset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.82/1.03  thf('8', plain,
% 0.82/1.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.82/1.03         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.82/1.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.82/1.03  thf('9', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((k9_subset_1 @ sk_A @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.82/1.03           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['7', '8'])).
% 0.82/1.03  thf('10', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(d5_subset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.82/1.03  thf('11', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i]:
% 0.82/1.03         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.82/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.82/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['10', '11'])).
% 0.82/1.03  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      (![X11 : $i, X12 : $i]:
% 0.82/1.03         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.82/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.82/1.03      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.82/1.03  thf('15', plain,
% 0.82/1.03      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['13', '14'])).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i]:
% 0.82/1.03         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.82/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.82/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.82/1.03         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['15', '16'])).
% 0.82/1.03  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(involutiveness_k3_subset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.03       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (![X13 : $i, X14 : $i]:
% 0.82/1.03         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.82/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.82/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.82/1.03  thf('20', plain,
% 0.82/1.03      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['18', '19'])).
% 0.82/1.03  thf('21', plain,
% 0.82/1.03      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.82/1.03      inference('demod', [status(thm)], ['17', '20'])).
% 0.82/1.03  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('23', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i]:
% 0.82/1.03         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.82/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.82/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.82/1.03  thf('24', plain,
% 0.82/1.03      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.82/1.03  thf(t48_xboole_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.82/1.03  thf('25', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.82/1.03           = (k3_xboole_0 @ X7 @ X8))),
% 0.82/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.03  thf('26', plain,
% 0.82/1.03      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.82/1.03         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup+', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.82/1.03  thf('27', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf('28', plain,
% 0.82/1.03      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.82/1.03         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.82/1.03      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.03  thf('29', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.82/1.03      inference('sup+', [status(thm)], ['21', '28'])).
% 0.82/1.03  thf('30', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf(t111_xboole_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.82/1.03       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.82/1.03  thf('31', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X4) @ (k3_xboole_0 @ X3 @ X4))
% 0.82/1.03           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4))),
% 0.82/1.03      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.82/1.03  thf('32', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.82/1.03           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.82/1.03      inference('sup+', [status(thm)], ['30', '31'])).
% 0.82/1.03  thf('33', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.82/1.03           = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.82/1.03      inference('sup+', [status(thm)], ['29', '32'])).
% 0.82/1.03  thf('34', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf(t47_xboole_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.82/1.03  thf('35', plain,
% 0.82/1.03      (![X5 : $i, X6 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.82/1.03           = (k4_xboole_0 @ X5 @ X6))),
% 0.82/1.03      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.82/1.03  thf('36', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.82/1.03           = (k4_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('sup+', [status(thm)], ['34', '35'])).
% 0.82/1.03  thf('37', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf('38', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((k4_xboole_0 @ sk_B @ X0)
% 0.82/1.03           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.82/1.03      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.82/1.03  thf('39', plain,
% 0.82/1.03      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.82/1.03         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['12', '38'])).
% 0.82/1.03  thf('40', plain,
% 0.82/1.03      (((k4_xboole_0 @ sk_B @ sk_C) != (k4_xboole_0 @ sk_B @ sk_C))),
% 0.82/1.03      inference('demod', [status(thm)], ['4', '9', '39'])).
% 0.82/1.03  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.82/1.03  
% 0.82/1.03  % SZS output end Refutation
% 0.82/1.03  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
