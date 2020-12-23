%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JCZOtAMUwd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:31 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 184 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  618 (1353 expanded)
%              Number of equality atoms :   69 ( 153 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ( k1_subset_1 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X24: $i] :
      ( X24
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X26 @ X25 ) @ ( k3_subset_1 @ X26 @ X27 ) )
      | ( r1_tarski @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('14',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('31',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_A )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('41',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('42',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('51',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['38','49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['36','51'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['23','58'])).

thf('60',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('61',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('62',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','49'])).

thf('64',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JCZOtAMUwd
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 609 iterations in 0.128s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(t39_subset_1, conjecture,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.36/0.58         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i]:
% 0.36/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.36/0.58            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.36/0.58  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t4_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.58  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X22 : $i, X23 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.36/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.36/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.58  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.58  thf('4', plain, (![X17 : $i]: ((k1_subset_1 @ X17) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.36/0.58  thf(t22_subset_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X24 : $i]:
% 0.36/0.58         ((k2_subset_1 @ X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.36/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.58  thf('6', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X24 : $i]: ((X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.36/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('8', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['4', '7'])).
% 0.36/0.58  thf('9', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['3', '8'])).
% 0.36/0.58  thf(t31_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ![C:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58           ( ( r1_tarski @ B @ C ) <=>
% 0.36/0.58             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.36/0.58          | ~ (r1_tarski @ (k3_subset_1 @ X26 @ X25) @ 
% 0.36/0.58               (k3_subset_1 @ X26 @ X27))
% 0.36/0.58          | (r1_tarski @ X27 @ X25)
% 0.36/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.36/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.58  thf('12', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.36/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.58  thf(dt_k2_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X21 : $i]: (m1_subset_1 @ (k2_subset_1 @ X21) @ (k1_zfmisc_1 @ X21))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.58  thf('14', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('15', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.36/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 0.36/0.58      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.36/0.58  thf('17', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '16'])).
% 0.36/0.58  thf(t28_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i]:
% 0.36/0.58         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.58  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.58  thf('21', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.58  thf(t22_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.36/0.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.36/0.58  thf('23', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.36/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.36/0.58        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.36/0.58      inference('split', [status(esa)], ['24'])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i]:
% 0.36/0.58         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.36/0.58          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.36/0.58          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.36/0.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      ((((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.36/0.58  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d5_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X19 : $i, X20 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.36/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.58  thf(t39_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.36/0.58           = (k2_xboole_0 @ X9 @ X10))),
% 0.36/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      ((((k2_xboole_0 @ sk_B @ sk_A) = (sk_B)))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.36/0.58        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.36/0.58       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.58      inference('split', [status(esa)], ['37'])).
% 0.36/0.58  thf('39', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['3', '8'])).
% 0.36/0.58  thf('40', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('split', [status(esa)], ['24'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.58         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.36/0.58      inference('split', [status(esa)], ['37'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.36/0.58         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.36/0.58             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.36/0.58         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.36/0.58             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.36/0.58         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.36/0.58             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['39', '46'])).
% 0.36/0.58  thf('48', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.36/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.36/0.58       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.36/0.58       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['24'])).
% 0.36/0.58  thf('51', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['38', '49', '50'])).
% 0.36/0.58  thf('52', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['36', '51'])).
% 0.36/0.58  thf(commutativity_k2_tarski, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (![X11 : $i, X12 : $i]:
% 0.36/0.58         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.36/0.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.58  thf(l51_zfmisc_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X15 : $i, X16 : $i]:
% 0.36/0.58         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.36/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.58      inference('sup+', [status(thm)], ['53', '54'])).
% 0.36/0.58  thf('56', plain,
% 0.36/0.58      (![X15 : $i, X16 : $i]:
% 0.36/0.58         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.36/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.58      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.58  thf('58', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['52', '57'])).
% 0.36/0.58  thf('59', plain, (((sk_A) = (sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['23', '58'])).
% 0.36/0.58  thf('60', plain,
% 0.36/0.58      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.36/0.58         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('split', [status(esa)], ['37'])).
% 0.36/0.58  thf('61', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('62', plain,
% 0.36/0.58      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.58  thf('63', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['38', '49'])).
% 0.36/0.58  thf('64', plain, (((sk_B) != (sk_A))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.36/0.58  thf('65', plain, ($false),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
