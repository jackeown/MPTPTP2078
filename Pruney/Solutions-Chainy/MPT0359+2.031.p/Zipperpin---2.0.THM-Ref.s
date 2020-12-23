%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9zQMGztpB0

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 254 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  609 (2011 expanded)
%              Number of equality atoms :   68 ( 196 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('20',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('21',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('22',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('36',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['19','34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['11','60'])).

thf('62',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('63',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['19','34'])).

thf('66',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9zQMGztpB0
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 345 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(t39_subset_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.54         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.54            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d2_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X19 @ X20)
% 0.20/0.54          | (r2_hidden @ X19 @ X20)
% 0.20/0.54          | (v1_xboole_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.54        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(fc1_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.54  thf('3', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.54  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(d1_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.54          | (r1_tarski @ X17 @ X15)
% 0.20/0.54          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X15 : $i, X17 : $i]:
% 0.20/0.54         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.54  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.54        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.54          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.54          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.54        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.54       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['18'])).
% 0.20/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.54  thf('20', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['12'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf(d5_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf(t36_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['18'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.54       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.54       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['12'])).
% 0.20/0.54  thf('36', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['19', '34', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.54         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['17', '36'])).
% 0.20/0.54  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf(t100_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.54           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.20/0.54         = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['37', '44', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.54           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.20/0.54         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf(t98_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X12 @ X13)
% 0.20/0.54           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.20/0.54         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf(t12_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]:
% 0.20/0.54         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.54  thf('54', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((sk_A) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['51', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['48', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf('58', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.54      inference('sup+', [status(thm)], ['56', '57'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('60', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['11', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.54         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['18'])).
% 0.20/0.54  thf('63', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['19', '34'])).
% 0.20/0.54  thf('66', plain, (((sk_B) != (sk_A))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['64', '65'])).
% 0.20/0.54  thf('67', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['61', '66'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
