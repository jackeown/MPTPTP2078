%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VACWlUZUEa

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   66 (  84 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  482 ( 711 expanded)
%              Number of equality atoms :   47 (  64 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k6_subset_1 @ X15 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['24','34','35'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k6_subset_1 @ X5 @ X6 ) )
      = ( k6_subset_1 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k6_subset_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['12','15','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VACWlUZUEa
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 448 iterations in 0.226s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.52/0.73  thf(t32_subset_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73       ( ![C:$i]:
% 0.52/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.52/0.73             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i]:
% 0.52/0.73        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73          ( ![C:$i]:
% 0.52/0.73            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.52/0.73                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.52/0.73         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(d5_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.52/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.73  thf(redefinition_k6_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.52/0.73         != (k9_subset_1 @ sk_A @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '5'])).
% 0.52/0.73  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k7_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.52/0.73          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.52/0.73          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k6_subset_1 @ X15 @ X17)))),
% 0.52/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (((k6_subset_1 @ sk_B @ sk_C)
% 0.52/0.73         != (k9_subset_1 @ sk_A @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.52/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.52/0.73  thf(dt_k6_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i]:
% 0.52/0.73         (m1_subset_1 @ (k6_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.52/0.73  thf(redefinition_k9_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.52/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((k9_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.73           = (k3_xboole_0 @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.73  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(involutiveness_k3_subset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.73       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i]:
% 0.52/0.73         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.52/0.73          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.73  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.52/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (((k3_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['18', '23'])).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i]:
% 0.52/0.73         (m1_subset_1 @ (k6_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.52/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         (((k3_subset_1 @ X7 @ X8) = (k6_subset_1 @ X7 @ X8))
% 0.52/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.73      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.73           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['25', '28'])).
% 0.52/0.73  thf(t48_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.52/0.73           = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X2 @ (k6_subset_1 @ X2 @ X3))
% 0.52/0.73           = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('demod', [status(thm)], ['29', '33'])).
% 0.52/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('36', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '34', '35'])).
% 0.52/0.73  thf(t49_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.52/0.73       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.52/0.73           = (k4_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6))),
% 0.52/0.73      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X4 @ (k6_subset_1 @ X5 @ X6))
% 0.52/0.73           = (k6_subset_1 @ (k3_xboole_0 @ X4 @ X5) @ X6))),
% 0.52/0.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ X0))
% 0.52/0.73           = (k6_subset_1 @ sk_B @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['36', '40'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (((k6_subset_1 @ sk_B @ sk_C) != (k6_subset_1 @ sk_B @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['12', '15', '41'])).
% 0.52/0.73  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
