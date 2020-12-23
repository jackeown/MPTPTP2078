%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HPvC5e5czf

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:46 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 495 expanded)
%              Number of leaves         :   36 ( 174 expanded)
%              Depth                    :   14
%              Number of atoms          :  758 (3608 expanded)
%              Number of equality atoms :   89 ( 443 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ X57 @ X58 )
      | ( r2_hidden @ X57 @ X59 )
      | ( X59
       != ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r2_hidden @ X57 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X57 @ X58 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','57'])).

thf('59',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['37','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','61','68'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','61','68'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('71',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X62 @ X63 ) )
      = ( k2_xboole_0 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('74',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['70','75'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('77',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','78'])).

thf('80',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','78'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('81',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['14','79','80','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HPvC5e5czf
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.49/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.69  % Solved by: fo/fo7.sh
% 1.49/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.69  % done 1786 iterations in 1.215s
% 1.49/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.69  % SZS output start Refutation
% 1.49/1.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.49/1.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.49/1.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.49/1.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.49/1.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.49/1.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.49/1.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.49/1.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.49/1.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.49/1.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.69  thf(t1_zfmisc_1, axiom,
% 1.49/1.69    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 1.49/1.69  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 1.49/1.69  thf(t2_boole, axiom,
% 1.49/1.69    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.49/1.69  thf('1', plain,
% 1.49/1.69      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [t2_boole])).
% 1.49/1.69  thf(t17_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.49/1.69  thf('2', plain,
% 1.49/1.69      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 1.49/1.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.49/1.69  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.69      inference('sup+', [status(thm)], ['1', '2'])).
% 1.49/1.69  thf(d1_zfmisc_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.49/1.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.49/1.69  thf('4', plain,
% 1.49/1.69      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.49/1.69         (~ (r1_tarski @ X57 @ X58)
% 1.49/1.69          | (r2_hidden @ X57 @ X59)
% 1.49/1.69          | ((X59) != (k1_zfmisc_1 @ X58)))),
% 1.49/1.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.49/1.69  thf('5', plain,
% 1.49/1.69      (![X57 : $i, X58 : $i]:
% 1.49/1.69         ((r2_hidden @ X57 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X57 @ X58))),
% 1.49/1.69      inference('simplify', [status(thm)], ['4'])).
% 1.49/1.69  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['3', '5'])).
% 1.49/1.69  thf('7', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['0', '6'])).
% 1.49/1.69  thf(d10_xboole_0, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.49/1.69  thf('8', plain,
% 1.49/1.69      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 1.49/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.69  thf('9', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 1.49/1.69      inference('simplify', [status(thm)], ['8'])).
% 1.49/1.69  thf(t28_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.49/1.69  thf('10', plain,
% 1.49/1.69      (![X16 : $i, X17 : $i]:
% 1.49/1.69         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.49/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.49/1.69  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.69  thf(t4_xboole_0, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.49/1.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.49/1.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.49/1.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.49/1.69  thf('12', plain,
% 1.49/1.69      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.49/1.69         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.49/1.69          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.49/1.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.69  thf('13', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['11', '12'])).
% 1.49/1.69  thf('14', plain,
% 1.49/1.69      (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['7', '13'])).
% 1.49/1.69  thf(t49_zfmisc_1, conjecture,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.49/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.69    (~( ![A:$i,B:$i]:
% 1.49/1.69        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 1.49/1.69    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 1.49/1.69  thf('15', plain,
% 1.49/1.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.69  thf('16', plain,
% 1.49/1.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.69  thf(commutativity_k3_xboole_0, axiom,
% 1.49/1.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.49/1.69  thf('17', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.49/1.69  thf(t94_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( k2_xboole_0 @ A @ B ) =
% 1.49/1.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.49/1.69  thf('18', plain,
% 1.49/1.69      (![X27 : $i, X28 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X27 @ X28)
% 1.49/1.69           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 1.49/1.69              (k3_xboole_0 @ X27 @ X28)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.49/1.69  thf(t91_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i,C:$i]:
% 1.49/1.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.49/1.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.49/1.69  thf('19', plain,
% 1.49/1.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.49/1.69           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.69  thf('20', plain,
% 1.49/1.69      (![X27 : $i, X28 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X27 @ X28)
% 1.49/1.69           = (k5_xboole_0 @ X27 @ 
% 1.49/1.69              (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X27 @ X28))))),
% 1.49/1.69      inference('demod', [status(thm)], ['18', '19'])).
% 1.49/1.69  thf('21', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X0 @ X1)
% 1.49/1.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.49/1.69      inference('sup+', [status(thm)], ['17', '20'])).
% 1.49/1.69  thf(t100_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.49/1.69  thf('22', plain,
% 1.49/1.69      (![X12 : $i, X13 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ X12 @ X13)
% 1.49/1.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.69  thf('23', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X0 @ X1)
% 1.49/1.69           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('demod', [status(thm)], ['21', '22'])).
% 1.49/1.69  thf(t92_xboole_1, axiom,
% 1.49/1.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.49/1.69  thf('24', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.69  thf('25', plain,
% 1.49/1.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.49/1.69           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.49/1.69  thf(commutativity_k5_xboole_0, axiom,
% 1.49/1.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.49/1.69  thf('26', plain,
% 1.49/1.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.49/1.69  thf('27', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.49/1.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['25', '26'])).
% 1.49/1.69  thf('28', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 1.49/1.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['24', '27'])).
% 1.49/1.69  thf(t5_boole, axiom,
% 1.49/1.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.49/1.69  thf('29', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.49/1.69      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.69  thf('30', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('demod', [status(thm)], ['28', '29'])).
% 1.49/1.69  thf('31', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ X0 @ X1)
% 1.49/1.69           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['23', '30'])).
% 1.49/1.69  thf('32', plain,
% 1.49/1.69      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 1.49/1.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['16', '31'])).
% 1.49/1.69  thf('33', plain,
% 1.49/1.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.49/1.69  thf('34', plain,
% 1.49/1.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.49/1.69  thf('35', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.49/1.69      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.69  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['34', '35'])).
% 1.49/1.69  thf('37', plain,
% 1.49/1.69      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.49/1.69      inference('demod', [status(thm)], ['32', '33', '36'])).
% 1.49/1.69  thf(t36_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.49/1.69  thf('38', plain,
% 1.49/1.69      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.49/1.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.69  thf('39', plain,
% 1.49/1.69      (![X16 : $i, X17 : $i]:
% 1.49/1.69         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.49/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.49/1.69  thf('40', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.49/1.69           = (k4_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('sup-', [status(thm)], ['38', '39'])).
% 1.49/1.69  thf('41', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.49/1.69  thf('42', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.49/1.69           = (k4_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('demod', [status(thm)], ['40', '41'])).
% 1.49/1.69  thf('43', plain,
% 1.49/1.69      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 1.49/1.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.49/1.69  thf('44', plain,
% 1.49/1.69      (![X16 : $i, X17 : $i]:
% 1.49/1.69         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.49/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.49/1.69  thf('45', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.49/1.69           = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('sup-', [status(thm)], ['43', '44'])).
% 1.49/1.69  thf('46', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.49/1.69  thf('47', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.49/1.69           = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('demod', [status(thm)], ['45', '46'])).
% 1.49/1.69  thf('48', plain,
% 1.49/1.69      (![X12 : $i, X13 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ X12 @ X13)
% 1.49/1.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.69  thf('49', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.49/1.69           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['47', '48'])).
% 1.49/1.69  thf('50', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.49/1.69  thf('51', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.49/1.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['25', '26'])).
% 1.49/1.69  thf('52', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.49/1.69           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['50', '51'])).
% 1.49/1.69  thf('53', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.49/1.69      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.69  thf('54', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.49/1.69      inference('demod', [status(thm)], ['52', '53'])).
% 1.49/1.69  thf('55', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.49/1.69           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 1.49/1.69      inference('sup+', [status(thm)], ['49', '54'])).
% 1.49/1.69  thf('56', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X0 @ X1)
% 1.49/1.69           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('demod', [status(thm)], ['21', '22'])).
% 1.49/1.69  thf('57', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.49/1.69      inference('demod', [status(thm)], ['55', '56'])).
% 1.49/1.69  thf('58', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.49/1.69      inference('sup+', [status(thm)], ['42', '57'])).
% 1.49/1.69  thf('59', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 1.49/1.69      inference('sup+', [status(thm)], ['37', '58'])).
% 1.49/1.69  thf('60', plain,
% 1.49/1.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.69  thf('61', plain, (((sk_B) = (k1_xboole_0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['59', '60'])).
% 1.49/1.69  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['34', '35'])).
% 1.49/1.69  thf('63', plain,
% 1.49/1.69      (![X27 : $i, X28 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X27 @ X28)
% 1.49/1.69           = (k5_xboole_0 @ X27 @ 
% 1.49/1.69              (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X27 @ X28))))),
% 1.49/1.69      inference('demod', [status(thm)], ['18', '19'])).
% 1.49/1.69  thf('64', plain,
% 1.49/1.69      (![X0 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.49/1.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['62', '63'])).
% 1.49/1.69  thf('65', plain,
% 1.49/1.69      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [t2_boole])).
% 1.49/1.69  thf('66', plain,
% 1.49/1.69      (![X0 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.49/1.69      inference('demod', [status(thm)], ['64', '65'])).
% 1.49/1.69  thf('67', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.49/1.69      inference('cnf', [status(esa)], [t5_boole])).
% 1.49/1.69  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['66', '67'])).
% 1.49/1.69  thf('69', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.49/1.69      inference('demod', [status(thm)], ['15', '61', '68'])).
% 1.49/1.69  thf('70', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.49/1.69      inference('demod', [status(thm)], ['15', '61', '68'])).
% 1.49/1.69  thf(t69_enumset1, axiom,
% 1.49/1.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.49/1.69  thf('71', plain,
% 1.49/1.69      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 1.49/1.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.49/1.69  thf(l51_zfmisc_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.49/1.69  thf('72', plain,
% 1.49/1.69      (![X62 : $i, X63 : $i]:
% 1.49/1.69         ((k3_tarski @ (k2_tarski @ X62 @ X63)) = (k2_xboole_0 @ X62 @ X63))),
% 1.49/1.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.49/1.69  thf('73', plain,
% 1.49/1.69      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['71', '72'])).
% 1.49/1.69  thf(idempotence_k2_xboole_0, axiom,
% 1.49/1.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.49/1.69  thf('74', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 1.49/1.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.49/1.69  thf('75', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.49/1.69      inference('demod', [status(thm)], ['73', '74'])).
% 1.49/1.69  thf('76', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 1.49/1.69      inference('sup+', [status(thm)], ['70', '75'])).
% 1.49/1.69  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.49/1.69  thf('77', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.69      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 1.49/1.69  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['76', '77'])).
% 1.49/1.69  thf('79', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.69      inference('demod', [status(thm)], ['69', '78'])).
% 1.49/1.69  thf('80', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.69      inference('demod', [status(thm)], ['69', '78'])).
% 1.49/1.69  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.49/1.69  thf('81', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 1.49/1.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.49/1.69  thf('82', plain,
% 1.49/1.69      (![X5 : $i, X6 : $i]:
% 1.49/1.69         ((r1_xboole_0 @ X5 @ X6)
% 1.49/1.69          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.69  thf('83', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.49/1.69  thf('84', plain,
% 1.49/1.69      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.49/1.69         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.49/1.69          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.49/1.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.69  thf('85', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.69         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.49/1.69          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('sup-', [status(thm)], ['83', '84'])).
% 1.49/1.69  thf('86', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.69      inference('sup-', [status(thm)], ['82', '85'])).
% 1.49/1.69  thf('87', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.49/1.69      inference('sup-', [status(thm)], ['81', '86'])).
% 1.49/1.69  thf('88', plain, ($false),
% 1.49/1.69      inference('demod', [status(thm)], ['14', '79', '80', '87'])).
% 1.49/1.69  
% 1.49/1.69  % SZS output end Refutation
% 1.49/1.69  
% 1.49/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
