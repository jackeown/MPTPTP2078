%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cihJvwmMls

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:20 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 516 expanded)
%              Number of leaves         :   29 ( 181 expanded)
%              Depth                    :   15
%              Number of atoms          : 1018 (4247 expanded)
%              Number of equality atoms :   80 ( 316 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t36_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
             => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k3_subset_1 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X22 @ ( k3_subset_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X19: $i] :
      ( X19
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['15','20','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','30'])).

thf('32',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k3_subset_1 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X22 @ ( k3_subset_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('53',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('58',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('60',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k3_subset_1 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X22 @ ( k3_subset_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k6_subset_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['65','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','84'])).

thf('86',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k6_subset_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('95',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','95'])).

thf('97',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','96'])).

thf('98',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('100',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('102',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('104',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('109',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['97','104','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['31','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cihJvwmMls
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 764 iterations in 0.229s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.52/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.52/0.71  thf(t36_subset_1, conjecture,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ![C:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.52/0.71             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i]:
% 0.52/0.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71          ( ![C:$i]:
% 0.52/0.71            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71              ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.52/0.71                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t36_subset_1])).
% 0.52/0.71  thf('0', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(d5_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.52/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.71  thf('4', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.52/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.71  thf(redefinition_k6_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('6', plain, (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.52/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.52/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.71  thf('7', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.71  thf('8', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t35_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ![C:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.52/0.71             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.52/0.71          | (r1_tarski @ X20 @ (k3_subset_1 @ X21 @ X22))
% 0.52/0.71          | ~ (r1_tarski @ X22 @ (k3_subset_1 @ X21 @ X20))
% 0.52/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.71          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.52/0.71          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.52/0.71      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.71          | ~ (r1_tarski @ X0 @ (k6_subset_1 @ sk_A @ sk_C))
% 0.52/0.71          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '13'])).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 0.52/0.71        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['7', '14'])).
% 0.52/0.71  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.71  thf('16', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.52/0.71  thf(t22_subset_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X19 : $i]:
% 0.52/0.71         ((k2_subset_1 @ X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.52/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.52/0.71  thf('18', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.52/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X19 : $i]: ((X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 0.52/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('20', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['16', '19'])).
% 0.52/0.71  thf(t4_subset_1, axiom,
% 0.52/0.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X23 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.52/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.71  thf('22', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.52/0.71      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.52/0.71  thf(t28_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('24', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.71  thf(t100_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X2 @ X3)
% 0.52/0.71           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X2 @ X3)
% 0.52/0.71           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.52/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X0 @ X1)
% 0.52/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['25', '28'])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['24', '29'])).
% 0.52/0.71  thf('31', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.52/0.71      inference('demod', [status(thm)], ['6', '30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['24', '29'])).
% 0.52/0.71  thf(t48_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.52/0.71           = (k3_xboole_0 @ X9 @ X10))),
% 0.52/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 0.52/0.71           = (k3_xboole_0 @ X9 @ X10))),
% 0.52/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.52/0.71         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['32', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.71  thf('39', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.52/0.71      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.52/0.71  thf('41', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.71  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.52/0.71          | (r1_tarski @ X20 @ (k3_subset_1 @ X21 @ X22))
% 0.52/0.71          | ~ (r1_tarski @ X22 @ (k3_subset_1 @ X21 @ X20))
% 0.52/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.71          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.52/0.71          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.71  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.52/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['47', '48'])).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.71          | ~ (r1_tarski @ X0 @ (k6_subset_1 @ sk_A @ sk_B))
% 0.52/0.71          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['44', '49'])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 0.52/0.71        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['41', '50'])).
% 0.52/0.71  thf('52', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['16', '19'])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      (![X23 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.52/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.71  thf('54', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.52/0.71      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('56', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X0 @ X1)
% 0.52/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['25', '28'])).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.52/0.71  thf(dt_k6_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k6_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 0.52/0.71           = (k3_xboole_0 @ X9 @ X10))),
% 0.52/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k6_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['61', '62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.52/0.71          | (r1_tarski @ X20 @ (k3_subset_1 @ X21 @ X22))
% 0.52/0.71          | ~ (r1_tarski @ X22 @ (k3_subset_1 @ X21 @ X20))
% 0.52/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.52/0.71          | ~ (r1_tarski @ X2 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 0.52/0.71          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_subset_1 @ X0 @ X2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['61', '62'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.52/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X13 @ X14) = (k6_subset_1 @ X13 @ X14))
% 0.52/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.52/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.71           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['66', '69'])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 0.52/0.71           = (k3_xboole_0 @ X9 @ X10))),
% 0.52/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 0.52/0.71           = (k3_xboole_0 @ X9 @ X10))),
% 0.52/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.71           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['71', '72'])).
% 0.52/0.71  thf(t36_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.52/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.52/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.52/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('demod', [status(thm)], ['76', '77'])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('80', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('81', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.71           = (k6_subset_1 @ X0 @ X1))),
% 0.52/0.71      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.52/0.71  thf('82', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.71           = (k6_subset_1 @ X1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['73', '81'])).
% 0.52/0.71  thf('83', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.71           = (k6_subset_1 @ X0 @ X1))),
% 0.52/0.71      inference('demod', [status(thm)], ['70', '82'])).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.52/0.71          | ~ (r1_tarski @ X2 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.71          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_subset_1 @ X0 @ X2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['65', '83'])).
% 0.52/0.71  thf('85', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.52/0.71           (k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)))
% 0.52/0.71          | ~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.52/0.71               (k6_subset_1 @ sk_A @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['60', '84'])).
% 0.52/0.71  thf('86', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.52/0.71  thf('87', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k6_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.52/0.71  thf('88', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X13 @ X14) = (k6_subset_1 @ X13 @ X14))
% 0.52/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.52/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.71  thf('89', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.71           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.52/0.71  thf('90', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 0.52/0.71           = (k3_xboole_0 @ X9 @ X10))),
% 0.52/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.52/0.71  thf('91', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.71           = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('demod', [status(thm)], ['89', '90'])).
% 0.52/0.71  thf('92', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.52/0.71         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['86', '91'])).
% 0.52/0.71  thf('93', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.71  thf('94', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.71  thf('95', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.52/0.71  thf('96', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.52/0.71          | ~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.52/0.71               (k6_subset_1 @ sk_A @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['85', '95'])).
% 0.52/0.71  thf('97', plain,
% 0.52/0.71      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.52/0.71        | (r1_tarski @ (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)) @ 
% 0.52/0.71           sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['40', '96'])).
% 0.52/0.71  thf('98', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('99', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('100', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.52/0.71      inference('demod', [status(thm)], ['98', '99'])).
% 0.52/0.71  thf('101', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.71  thf('102', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.52/0.71      inference('demod', [status(thm)], ['100', '101'])).
% 0.52/0.71  thf('103', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.52/0.71  thf('104', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.52/0.71      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.71  thf('105', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['24', '29'])).
% 0.52/0.71  thf('106', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.52/0.71           = (k6_subset_1 @ X0 @ X1))),
% 0.52/0.71      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.52/0.71  thf('107', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.52/0.71         = (k6_subset_1 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['105', '106'])).
% 0.52/0.71  thf('108', plain,
% 0.52/0.71      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['24', '29'])).
% 0.52/0.71  thf('109', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.52/0.71         = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.71      inference('demod', [status(thm)], ['107', '108'])).
% 0.52/0.71  thf('110', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.52/0.71      inference('demod', [status(thm)], ['97', '104', '109'])).
% 0.52/0.71  thf('111', plain, ($false), inference('demod', [status(thm)], ['31', '110'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
