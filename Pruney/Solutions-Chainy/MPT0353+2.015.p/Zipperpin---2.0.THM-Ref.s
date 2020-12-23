%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rVWdnPGYUe

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 179 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  630 (1764 expanded)
%              Number of equality atoms :   56 ( 134 expanded)
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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('14',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('32',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('46',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['29','34','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rVWdnPGYUe
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:49:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 1.22/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.22/1.46  % Solved by: fo/fo7.sh
% 1.22/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.46  % done 714 iterations in 1.016s
% 1.22/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.22/1.46  % SZS output start Refutation
% 1.22/1.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.22/1.46  thf(sk_C_type, type, sk_C: $i).
% 1.22/1.46  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.22/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.46  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.22/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.22/1.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.22/1.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.22/1.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.22/1.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.22/1.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.22/1.46  thf(t32_subset_1, conjecture,
% 1.22/1.46    (![A:$i,B:$i]:
% 1.22/1.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46       ( ![C:$i]:
% 1.22/1.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.22/1.46             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.22/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.46    (~( ![A:$i,B:$i]:
% 1.22/1.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46          ( ![C:$i]:
% 1.22/1.46            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46              ( ( k7_subset_1 @ A @ B @ C ) =
% 1.22/1.46                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 1.22/1.46    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 1.22/1.46  thf('0', plain,
% 1.22/1.46      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 1.22/1.46         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf(d5_subset_1, axiom,
% 1.22/1.46    (![A:$i,B:$i]:
% 1.22/1.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.22/1.46  thf('2', plain,
% 1.22/1.46      (![X9 : $i, X10 : $i]:
% 1.22/1.46         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 1.22/1.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.46  thf('3', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.22/1.46      inference('sup-', [status(thm)], ['1', '2'])).
% 1.22/1.46  thf('4', plain,
% 1.22/1.46      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 1.22/1.46         != (k9_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.22/1.46      inference('demod', [status(thm)], ['0', '3'])).
% 1.22/1.46  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf(involutiveness_k3_subset_1, axiom,
% 1.22/1.46    (![A:$i,B:$i]:
% 1.22/1.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.22/1.46  thf('6', plain,
% 1.22/1.46      (![X13 : $i, X14 : $i]:
% 1.22/1.46         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 1.22/1.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.22/1.46      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.22/1.46  thf('7', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 1.22/1.46      inference('sup-', [status(thm)], ['5', '6'])).
% 1.22/1.46  thf('8', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.22/1.46      inference('sup-', [status(thm)], ['1', '2'])).
% 1.22/1.46  thf('9', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 1.22/1.46      inference('demod', [status(thm)], ['7', '8'])).
% 1.22/1.46  thf('10', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf(dt_k3_subset_1, axiom,
% 1.22/1.46    (![A:$i,B:$i]:
% 1.22/1.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.22/1.46  thf('11', plain,
% 1.22/1.46      (![X11 : $i, X12 : $i]:
% 1.22/1.46         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 1.22/1.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.22/1.46      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.22/1.46  thf('12', plain,
% 1.22/1.46      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('sup-', [status(thm)], ['10', '11'])).
% 1.22/1.46  thf('13', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.22/1.46      inference('sup-', [status(thm)], ['1', '2'])).
% 1.22/1.46  thf('14', plain,
% 1.22/1.46      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('demod', [status(thm)], ['12', '13'])).
% 1.22/1.46  thf('15', plain,
% 1.22/1.46      (![X9 : $i, X10 : $i]:
% 1.22/1.46         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 1.22/1.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.46  thf('16', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 1.22/1.46         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['14', '15'])).
% 1.22/1.46  thf(t48_xboole_1, axiom,
% 1.22/1.46    (![A:$i,B:$i]:
% 1.22/1.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.22/1.46  thf('17', plain,
% 1.22/1.46      (![X7 : $i, X8 : $i]:
% 1.22/1.46         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.22/1.46           = (k3_xboole_0 @ X7 @ X8))),
% 1.22/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.22/1.46  thf(commutativity_k3_xboole_0, axiom,
% 1.22/1.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.22/1.46  thf('18', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.22/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.46  thf('19', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 1.22/1.46         = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.22/1.46      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.22/1.46  thf('20', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.22/1.46      inference('sup+', [status(thm)], ['9', '19'])).
% 1.22/1.46  thf('21', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.22/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.46  thf(t100_xboole_1, axiom,
% 1.22/1.46    (![A:$i,B:$i]:
% 1.22/1.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.22/1.46  thf('22', plain,
% 1.22/1.46      (![X2 : $i, X3 : $i]:
% 1.22/1.46         ((k4_xboole_0 @ X2 @ X3)
% 1.22/1.46           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.22/1.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.46  thf('23', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((k4_xboole_0 @ X0 @ X1)
% 1.22/1.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.22/1.46      inference('sup+', [status(thm)], ['21', '22'])).
% 1.22/1.46  thf('24', plain,
% 1.22/1.46      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 1.22/1.46      inference('sup+', [status(thm)], ['20', '23'])).
% 1.22/1.46  thf('25', plain,
% 1.22/1.46      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 1.22/1.46         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))),
% 1.22/1.46      inference('demod', [status(thm)], ['4', '24'])).
% 1.22/1.46  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf(redefinition_k7_subset_1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i]:
% 1.22/1.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.22/1.46  thf('27', plain,
% 1.22/1.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.46         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 1.22/1.46          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 1.22/1.46      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.22/1.46  thf('28', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 1.22/1.46      inference('sup-', [status(thm)], ['26', '27'])).
% 1.22/1.46  thf('29', plain,
% 1.22/1.46      (((k4_xboole_0 @ sk_B @ sk_C)
% 1.22/1.46         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))),
% 1.22/1.46      inference('demod', [status(thm)], ['25', '28'])).
% 1.22/1.46  thf('30', plain,
% 1.22/1.46      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('demod', [status(thm)], ['12', '13'])).
% 1.22/1.46  thf('31', plain,
% 1.22/1.46      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 1.22/1.46      inference('sup+', [status(thm)], ['20', '23'])).
% 1.22/1.46  thf('32', plain,
% 1.22/1.46      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('demod', [status(thm)], ['30', '31'])).
% 1.22/1.46  thf(redefinition_k9_subset_1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i]:
% 1.22/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.46       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.22/1.46  thf('33', plain,
% 1.22/1.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.22/1.46         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 1.22/1.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.22/1.46      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.22/1.46  thf('34', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         ((k9_subset_1 @ sk_A @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))
% 1.22/1.46           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['32', '33'])).
% 1.22/1.46  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf('36', plain,
% 1.22/1.46      (![X13 : $i, X14 : $i]:
% 1.22/1.46         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 1.22/1.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.22/1.46      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.22/1.46  thf('37', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.22/1.46      inference('sup-', [status(thm)], ['35', '36'])).
% 1.22/1.46  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf('39', plain,
% 1.22/1.46      (![X9 : $i, X10 : $i]:
% 1.22/1.46         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 1.22/1.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.46  thf('40', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.22/1.46      inference('sup-', [status(thm)], ['38', '39'])).
% 1.22/1.46  thf('41', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 1.22/1.46      inference('demod', [status(thm)], ['37', '40'])).
% 1.22/1.46  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf('43', plain,
% 1.22/1.46      (![X11 : $i, X12 : $i]:
% 1.22/1.46         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 1.22/1.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.22/1.46      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.22/1.46  thf('44', plain,
% 1.22/1.46      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('sup-', [status(thm)], ['42', '43'])).
% 1.22/1.46  thf('45', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.22/1.46      inference('sup-', [status(thm)], ['38', '39'])).
% 1.22/1.46  thf('46', plain,
% 1.22/1.46      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.22/1.46      inference('demod', [status(thm)], ['44', '45'])).
% 1.22/1.46  thf('47', plain,
% 1.22/1.46      (![X9 : $i, X10 : $i]:
% 1.22/1.46         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 1.22/1.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.46  thf('48', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.22/1.46         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['46', '47'])).
% 1.22/1.46  thf('49', plain,
% 1.22/1.46      (![X7 : $i, X8 : $i]:
% 1.22/1.46         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.22/1.46           = (k3_xboole_0 @ X7 @ X8))),
% 1.22/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.22/1.46  thf('50', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.22/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.46  thf('51', plain,
% 1.22/1.46      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.22/1.46         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.22/1.46      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.22/1.46  thf('52', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.22/1.46      inference('sup+', [status(thm)], ['41', '51'])).
% 1.22/1.46  thf('53', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.22/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.46  thf(t112_xboole_1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i]:
% 1.22/1.46     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.22/1.46       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.22/1.46  thf('54', plain,
% 1.22/1.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.22/1.46         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.22/1.46           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 1.22/1.46      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.22/1.46  thf('55', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.46         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.22/1.46           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.22/1.46      inference('sup+', [status(thm)], ['53', '54'])).
% 1.22/1.46  thf('56', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 1.22/1.46           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.22/1.46      inference('sup+', [status(thm)], ['52', '55'])).
% 1.22/1.46  thf('57', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((k4_xboole_0 @ X0 @ X1)
% 1.22/1.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.22/1.46      inference('sup+', [status(thm)], ['21', '22'])).
% 1.22/1.46  thf('58', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.22/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.46  thf('59', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         ((k4_xboole_0 @ sk_B @ X0)
% 1.22/1.46           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.22/1.46      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.22/1.46  thf('60', plain,
% 1.22/1.46      (((k4_xboole_0 @ sk_B @ sk_C) != (k4_xboole_0 @ sk_B @ sk_C))),
% 1.22/1.46      inference('demod', [status(thm)], ['29', '34', '59'])).
% 1.22/1.46  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 1.22/1.46  
% 1.22/1.46  % SZS output end Refutation
% 1.22/1.46  
% 1.30/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
