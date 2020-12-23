%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvaHmxgc4T

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:40 EST 2020

% Result     : Theorem 20.37s
% Output     : Refutation 20.37s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 611 expanded)
%              Number of leaves         :   30 ( 213 expanded)
%              Depth                    :   30
%              Number of atoms          : 1678 (5230 expanded)
%              Number of equality atoms :  190 ( 584 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ X40 @ ( k4_xboole_0 @ X37 @ X39 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X40 @ X37 ) @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X33 @ X35 ) @ ( k3_xboole_0 @ X34 @ X36 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X31 @ X30 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('56',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','60','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','67'])).

thf('69',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X37 @ X39 ) @ X38 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('78',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('80',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('83',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('95',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A )
    | ( r1_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('97',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('99',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('101',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('104',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['68','104'])).

thf('106',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,
    ( ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
      | ( k1_xboole_0 = sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('110',plain,
    ( ( ( k1_xboole_0 = sk_B_1 )
      | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('112',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
        = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
      | ( k1_xboole_0 = sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('115',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
        = sk_A )
      | ( k1_xboole_0 = sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X37 @ X39 ) @ X38 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('119',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('128',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('135',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X33 @ X35 ) @ ( k3_xboole_0 @ X34 @ X36 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X3 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('140',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['138','140'])).

thf('142',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['126','141'])).

thf('143',plain,
    ( ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( k1_xboole_0 = sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['115','142'])).

thf('144',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k1_xboole_0 = sk_B_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','67'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('148',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('150',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('152',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = sk_B_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('154',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['106'])).

thf('156',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('158',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('160',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('163',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = sk_A )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['126','141'])).

thf('165',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    r1_tarski @ sk_B_1 @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['106'])).

thf('169',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['167','168'])).

thf('170',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['145','169'])).

thf('171',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('172',plain,(
    ! [X31: $i] :
      ( ( k2_zfmisc_1 @ X31 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','170','172'])).

thf('174',plain,(
    $false ),
    inference(simplify,[status(thm)],['173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvaHmxgc4T
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:33:50 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 20.37/20.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.37/20.60  % Solved by: fo/fo7.sh
% 20.37/20.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.37/20.60  % done 9654 iterations in 20.137s
% 20.37/20.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.37/20.60  % SZS output start Refutation
% 20.37/20.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 20.37/20.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.37/20.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 20.37/20.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 20.37/20.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 20.37/20.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.37/20.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 20.37/20.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.37/20.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.37/20.60  thf(sk_A_type, type, sk_A: $i).
% 20.37/20.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.37/20.60  thf(sk_D_type, type, sk_D: $i).
% 20.37/20.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.37/20.60  thf(t138_zfmisc_1, conjecture,
% 20.37/20.60    (![A:$i,B:$i,C:$i,D:$i]:
% 20.37/20.60     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 20.37/20.60       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 20.37/20.60         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 20.37/20.60  thf(zf_stmt_0, negated_conjecture,
% 20.37/20.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 20.37/20.60        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 20.37/20.60          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 20.37/20.60            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 20.37/20.60    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 20.37/20.60  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.37/20.60  thf(t125_zfmisc_1, axiom,
% 20.37/20.60    (![A:$i,B:$i,C:$i]:
% 20.37/20.60     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 20.37/20.60         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 20.37/20.60       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 20.37/20.60         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 20.37/20.60  thf('1', plain,
% 20.37/20.60      (![X37 : $i, X39 : $i, X40 : $i]:
% 20.37/20.60         ((k2_zfmisc_1 @ X40 @ (k4_xboole_0 @ X37 @ X39))
% 20.37/20.60           = (k4_xboole_0 @ (k2_zfmisc_1 @ X40 @ X37) @ 
% 20.37/20.60              (k2_zfmisc_1 @ X40 @ X39)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 20.37/20.60  thf('2', plain,
% 20.37/20.60      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 20.37/20.60        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 20.37/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.37/20.60  thf(t28_xboole_1, axiom,
% 20.37/20.60    (![A:$i,B:$i]:
% 20.37/20.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 20.37/20.60  thf('3', plain,
% 20.37/20.60      (![X20 : $i, X21 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 20.37/20.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 20.37/20.60  thf('4', plain,
% 20.37/20.60      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 20.37/20.60         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['2', '3'])).
% 20.37/20.60  thf(commutativity_k3_xboole_0, axiom,
% 20.37/20.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 20.37/20.60  thf('5', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('6', plain,
% 20.37/20.60      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 20.37/20.60         (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 20.37/20.60      inference('demod', [status(thm)], ['4', '5'])).
% 20.37/20.60  thf(t16_xboole_1, axiom,
% 20.37/20.60    (![A:$i,B:$i,C:$i]:
% 20.37/20.60     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 20.37/20.60       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 20.37/20.60  thf('7', plain,
% 20.37/20.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 20.37/20.60           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 20.37/20.60  thf('8', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)
% 20.37/20.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 20.37/20.60              (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['6', '7'])).
% 20.37/20.60  thf('9', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf(t100_xboole_1, axiom,
% 20.37/20.60    (![A:$i,B:$i]:
% 20.37/20.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 20.37/20.60  thf('10', plain,
% 20.37/20.60      (![X13 : $i, X14 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X13 @ X14)
% 20.37/20.60           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.37/20.60  thf('11', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X0 @ X1)
% 20.37/20.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['9', '10'])).
% 20.37/20.60  thf('12', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0) @ 
% 20.37/20.60           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 20.37/20.60           = (k5_xboole_0 @ 
% 20.37/20.60              (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0) @ 
% 20.37/20.60              (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['8', '11'])).
% 20.37/20.60  thf(t49_xboole_1, axiom,
% 20.37/20.60    (![A:$i,B:$i,C:$i]:
% 20.37/20.60     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 20.37/20.60       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 20.37/20.60  thf('13', plain,
% 20.37/20.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 20.37/20.60           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 20.37/20.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 20.37/20.60  thf(t92_xboole_1, axiom,
% 20.37/20.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 20.37/20.60  thf('14', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 20.37/20.60  thf('15', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 20.37/20.60           (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))) = (k1_xboole_0))),
% 20.37/20.60      inference('demod', [status(thm)], ['12', '13', '14'])).
% 20.37/20.60  thf('16', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 20.37/20.60           (k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['1', '15'])).
% 20.37/20.60  thf(t123_zfmisc_1, axiom,
% 20.37/20.60    (![A:$i,B:$i,C:$i,D:$i]:
% 20.37/20.60     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 20.37/20.60       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 20.37/20.60  thf('17', plain,
% 20.37/20.60      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 20.37/20.60         ((k2_zfmisc_1 @ (k3_xboole_0 @ X33 @ X35) @ (k3_xboole_0 @ X34 @ X36))
% 20.37/20.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34) @ 
% 20.37/20.60              (k2_zfmisc_1 @ X35 @ X36)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 20.37/20.60  thf(t113_zfmisc_1, axiom,
% 20.37/20.60    (![A:$i,B:$i]:
% 20.37/20.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 20.37/20.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 20.37/20.60  thf('18', plain,
% 20.37/20.60      (![X30 : $i, X31 : $i]:
% 20.37/20.60         (((X30) = (k1_xboole_0))
% 20.37/20.60          | ((X31) = (k1_xboole_0))
% 20.37/20.60          | ((k2_zfmisc_1 @ X31 @ X30) != (k1_xboole_0)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 20.37/20.60  thf('19', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 20.37/20.60            != (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['17', '18'])).
% 20.37/20.60  thf('20', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k1_xboole_0) != (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['16', '19'])).
% 20.37/20.60  thf('21', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('22', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k1_xboole_0) != (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 20.37/20.60      inference('demod', [status(thm)], ['20', '21'])).
% 20.37/20.60  thf('23', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0)))),
% 20.37/20.60      inference('simplify', [status(thm)], ['22'])).
% 20.37/20.60  thf(idempotence_k3_xboole_0, axiom,
% 20.37/20.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 20.37/20.60  thf('24', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 20.37/20.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 20.37/20.60  thf('25', plain,
% 20.37/20.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 20.37/20.60           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 20.37/20.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 20.37/20.60  thf('26', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 20.37/20.60           = (k4_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['24', '25'])).
% 20.37/20.60  thf('27', plain,
% 20.37/20.60      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))
% 20.37/20.60        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['23', '26'])).
% 20.37/20.60  thf('28', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf(t4_xboole_0, axiom,
% 20.37/20.60    (![A:$i,B:$i]:
% 20.37/20.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 20.37/20.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 20.37/20.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 20.37/20.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 20.37/20.60  thf('29', plain,
% 20.37/20.60      (![X8 : $i, X9 : $i]:
% 20.37/20.60         ((r1_xboole_0 @ X8 @ X9)
% 20.37/20.60          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 20.37/20.60  thf('30', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 20.37/20.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 20.37/20.60  thf('31', plain,
% 20.37/20.60      (![X8 : $i, X10 : $i, X11 : $i]:
% 20.37/20.60         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 20.37/20.60          | ~ (r1_xboole_0 @ X8 @ X11))),
% 20.37/20.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 20.37/20.60  thf('32', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 20.37/20.60      inference('sup-', [status(thm)], ['30', '31'])).
% 20.37/20.60  thf('33', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((r1_xboole_0 @ X1 @ X0)
% 20.37/20.60          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['29', '32'])).
% 20.37/20.60  thf('34', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 20.37/20.60          | (r1_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['28', '33'])).
% 20.37/20.60  thf('35', plain,
% 20.37/20.60      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ k1_xboole_0)
% 20.37/20.60        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))
% 20.37/20.60        | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 20.37/20.60      inference('sup-', [status(thm)], ['27', '34'])).
% 20.37/20.60  thf('36', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('37', plain,
% 20.37/20.60      (![X13 : $i, X14 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X13 @ X14)
% 20.37/20.60           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.37/20.60  thf(commutativity_k5_xboole_0, axiom,
% 20.37/20.60    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 20.37/20.60  thf('38', plain,
% 20.37/20.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 20.37/20.60  thf(t5_boole, axiom,
% 20.37/20.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 20.37/20.60  thf('39', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 20.37/20.60      inference('cnf', [status(esa)], [t5_boole])).
% 20.37/20.60  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('41', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['37', '40'])).
% 20.37/20.60  thf('42', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf(d7_xboole_0, axiom,
% 20.37/20.60    (![A:$i,B:$i]:
% 20.37/20.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 20.37/20.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 20.37/20.60  thf('43', plain,
% 20.37/20.60      (![X4 : $i, X6 : $i]:
% 20.37/20.60         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 20.37/20.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 20.37/20.60  thf('44', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['42', '43'])).
% 20.37/20.60  thf('45', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 20.37/20.60          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 20.37/20.60      inference('sup-', [status(thm)], ['41', '44'])).
% 20.37/20.60  thf('46', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf(t17_xboole_1, axiom,
% 20.37/20.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 20.37/20.60  thf('47', plain,
% 20.37/20.60      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 20.37/20.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 20.37/20.60  thf('48', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 20.37/20.60      inference('sup+', [status(thm)], ['46', '47'])).
% 20.37/20.60  thf('49', plain,
% 20.37/20.60      (![X20 : $i, X21 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 20.37/20.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 20.37/20.60  thf('50', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 20.37/20.60           = (k3_xboole_0 @ X1 @ X0))),
% 20.37/20.60      inference('sup-', [status(thm)], ['48', '49'])).
% 20.37/20.60  thf('51', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('52', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 20.37/20.60           = (k3_xboole_0 @ X1 @ X0))),
% 20.37/20.60      inference('demod', [status(thm)], ['50', '51'])).
% 20.37/20.60  thf('53', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X0 @ X1)
% 20.37/20.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['9', '10'])).
% 20.37/20.60  thf('54', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 20.37/20.60           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['52', '53'])).
% 20.37/20.60  thf('55', plain,
% 20.37/20.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 20.37/20.60           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 20.37/20.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 20.37/20.60  thf('56', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 20.37/20.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 20.37/20.60  thf('57', plain,
% 20.37/20.60      (![X13 : $i, X14 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X13 @ X14)
% 20.37/20.60           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.37/20.60  thf('58', plain,
% 20.37/20.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['56', '57'])).
% 20.37/20.60  thf('59', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 20.37/20.60  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['58', '59'])).
% 20.37/20.60  thf('61', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['37', '40'])).
% 20.37/20.60  thf('62', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('63', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['61', '62'])).
% 20.37/20.60  thf('64', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 20.37/20.60  thf('65', plain,
% 20.37/20.60      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 20.37/20.60      inference('demod', [status(thm)], ['54', '55', '60', '63', '64'])).
% 20.37/20.60  thf('66', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 20.37/20.60      inference('demod', [status(thm)], ['45', '65'])).
% 20.37/20.60  thf('67', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 20.37/20.60      inference('simplify', [status(thm)], ['66'])).
% 20.37/20.60  thf('68', plain,
% 20.37/20.60      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))
% 20.37/20.60        | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 20.37/20.60      inference('demod', [status(thm)], ['35', '36', '67'])).
% 20.37/20.60  thf('69', plain,
% 20.37/20.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 20.37/20.60         ((k2_zfmisc_1 @ (k4_xboole_0 @ X37 @ X39) @ X38)
% 20.37/20.60           = (k4_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 20.37/20.60              (k2_zfmisc_1 @ X39 @ X38)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 20.37/20.60  thf('70', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 20.37/20.60           (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))) = (k1_xboole_0))),
% 20.37/20.60      inference('demod', [status(thm)], ['12', '13', '14'])).
% 20.37/20.60  thf('71', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 20.37/20.60           (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)) = (k1_xboole_0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['69', '70'])).
% 20.37/20.60  thf('72', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 20.37/20.60            != (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['17', '18'])).
% 20.37/20.60  thf('73', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k1_xboole_0) != (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['71', '72'])).
% 20.37/20.60  thf('74', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('75', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k1_xboole_0) != (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)) = (k1_xboole_0)))),
% 20.37/20.60      inference('demod', [status(thm)], ['73', '74'])).
% 20.37/20.60  thf('76', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)) = (k1_xboole_0))
% 20.37/20.60          | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 20.37/20.60      inference('simplify', [status(thm)], ['75'])).
% 20.37/20.60  thf('77', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 20.37/20.60           = (k4_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['24', '25'])).
% 20.37/20.60  thf('78', plain,
% 20.37/20.60      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))
% 20.37/20.60        | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['76', '77'])).
% 20.37/20.60  thf('79', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 20.37/20.60          | (r1_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['28', '33'])).
% 20.37/20.60  thf('80', plain,
% 20.37/20.60      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_D) @ k1_xboole_0)
% 20.37/20.60        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))
% 20.37/20.60        | (r1_xboole_0 @ sk_D @ sk_B_1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['78', '79'])).
% 20.37/20.60  thf('81', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('82', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 20.37/20.60      inference('simplify', [status(thm)], ['66'])).
% 20.37/20.60  thf('83', plain,
% 20.37/20.60      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))
% 20.37/20.60        | (r1_xboole_0 @ sk_D @ sk_B_1))),
% 20.37/20.60      inference('demod', [status(thm)], ['80', '81', '82'])).
% 20.37/20.60  thf('84', plain,
% 20.37/20.60      (![X13 : $i, X14 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X13 @ X14)
% 20.37/20.60           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.37/20.60  thf('85', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 20.37/20.60  thf(t91_xboole_1, axiom,
% 20.37/20.60    (![A:$i,B:$i,C:$i]:
% 20.37/20.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 20.37/20.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 20.37/20.60  thf('86', plain,
% 20.37/20.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 20.37/20.60         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 20.37/20.60           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 20.37/20.60  thf('87', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 20.37/20.60           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['85', '86'])).
% 20.37/20.60  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('89', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('demod', [status(thm)], ['87', '88'])).
% 20.37/20.60  thf('90', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X1 @ X0)
% 20.37/20.60           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['84', '89'])).
% 20.37/20.60  thf('91', plain,
% 20.37/20.60      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 20.37/20.60        | (r1_xboole_0 @ sk_D @ sk_B_1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['83', '90'])).
% 20.37/20.60  thf('92', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('93', plain,
% 20.37/20.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 20.37/20.60  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('95', plain,
% 20.37/20.60      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))
% 20.37/20.60        | (r1_xboole_0 @ sk_D @ sk_B_1))),
% 20.37/20.60      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 20.37/20.60  thf('96', plain,
% 20.37/20.60      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 20.37/20.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 20.37/20.60  thf('97', plain,
% 20.37/20.60      (((r1_tarski @ sk_A @ sk_C_1) | (r1_xboole_0 @ sk_D @ sk_B_1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['95', '96'])).
% 20.37/20.60  thf('98', plain,
% 20.37/20.60      (![X4 : $i, X5 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 20.37/20.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 20.37/20.60  thf('99', plain,
% 20.37/20.60      (((r1_tarski @ sk_A @ sk_C_1)
% 20.37/20.60        | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['97', '98'])).
% 20.37/20.60  thf('100', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X0 @ X1)
% 20.37/20.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['9', '10'])).
% 20.37/20.60  thf('101', plain,
% 20.37/20.60      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 20.37/20.60        | (r1_tarski @ sk_A @ sk_C_1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['99', '100'])).
% 20.37/20.60  thf('102', plain,
% 20.37/20.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 20.37/20.60  thf('103', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('104', plain,
% 20.37/20.60      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))
% 20.37/20.60        | (r1_tarski @ sk_A @ sk_C_1))),
% 20.37/20.60      inference('demod', [status(thm)], ['101', '102', '103'])).
% 20.37/20.60  thf('105', plain,
% 20.37/20.60      ((((k1_xboole_0) = (sk_B_1))
% 20.37/20.60        | (r1_xboole_0 @ sk_C_1 @ sk_A)
% 20.37/20.60        | (r1_tarski @ sk_A @ sk_C_1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['68', '104'])).
% 20.37/20.60  thf('106', plain,
% 20.37/20.60      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 20.37/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.37/20.60  thf('107', plain,
% 20.37/20.60      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('split', [status(esa)], ['106'])).
% 20.37/20.60  thf('108', plain,
% 20.37/20.60      ((((r1_xboole_0 @ sk_C_1 @ sk_A) | ((k1_xboole_0) = (sk_B_1))))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['105', '107'])).
% 20.37/20.60  thf('109', plain,
% 20.37/20.60      (![X4 : $i, X5 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 20.37/20.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 20.37/20.60  thf('110', plain,
% 20.37/20.60      (((((k1_xboole_0) = (sk_B_1))
% 20.37/20.60         | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['108', '109'])).
% 20.37/20.60  thf('111', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X0 @ X1)
% 20.37/20.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['9', '10'])).
% 20.37/20.60  thf('112', plain,
% 20.37/20.60      (((((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 20.37/20.60         | ((k1_xboole_0) = (sk_B_1)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['110', '111'])).
% 20.37/20.60  thf('113', plain,
% 20.37/20.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 20.37/20.60  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('115', plain,
% 20.37/20.60      (((((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A)) | ((k1_xboole_0) = (sk_B_1))))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('demod', [status(thm)], ['112', '113', '114'])).
% 20.37/20.60  thf('116', plain,
% 20.37/20.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 20.37/20.60         ((k2_zfmisc_1 @ (k4_xboole_0 @ X37 @ X39) @ X38)
% 20.37/20.60           = (k4_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 20.37/20.60              (k2_zfmisc_1 @ X39 @ X38)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 20.37/20.60  thf('117', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 20.37/20.60           = (k4_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['24', '25'])).
% 20.37/20.60  thf('118', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)
% 20.37/20.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 20.37/20.60              (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['6', '7'])).
% 20.37/20.60  thf('119', plain,
% 20.37/20.60      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 20.37/20.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 20.37/20.60  thf('120', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (r1_tarski @ (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0) @ 
% 20.37/20.60          (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 20.37/20.60      inference('sup+', [status(thm)], ['118', '119'])).
% 20.37/20.60  thf('121', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (r1_tarski @ (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0) @ 
% 20.37/20.60          (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 20.37/20.60      inference('sup+', [status(thm)], ['117', '120'])).
% 20.37/20.60  thf('122', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         (r1_tarski @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1) @ 
% 20.37/20.60          (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 20.37/20.60      inference('sup+', [status(thm)], ['116', '121'])).
% 20.37/20.60  thf('123', plain,
% 20.37/20.60      (![X20 : $i, X21 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 20.37/20.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 20.37/20.60  thf('124', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1) @ 
% 20.37/20.60           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 20.37/20.60           = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['122', '123'])).
% 20.37/20.60  thf('125', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('126', plain,
% 20.37/20.60      (![X0 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 20.37/20.60           (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))
% 20.37/20.60           = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))),
% 20.37/20.60      inference('demod', [status(thm)], ['124', '125'])).
% 20.37/20.60  thf('127', plain,
% 20.37/20.60      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 20.37/20.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 20.37/20.60  thf('128', plain,
% 20.37/20.60      (![X20 : $i, X21 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 20.37/20.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 20.37/20.60  thf('129', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 20.37/20.60           = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('sup-', [status(thm)], ['127', '128'])).
% 20.37/20.60  thf('130', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('131', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 20.37/20.60           = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('demod', [status(thm)], ['129', '130'])).
% 20.37/20.60  thf('132', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X0 @ X1)
% 20.37/20.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['9', '10'])).
% 20.37/20.60  thf('133', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 20.37/20.60           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['131', '132'])).
% 20.37/20.60  thf('134', plain,
% 20.37/20.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 20.37/20.60           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 20.37/20.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 20.37/20.60  thf('135', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 20.37/20.60  thf('136', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 20.37/20.60      inference('demod', [status(thm)], ['133', '134', '135'])).
% 20.37/20.60  thf('137', plain,
% 20.37/20.60      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 20.37/20.60         ((k2_zfmisc_1 @ (k3_xboole_0 @ X33 @ X35) @ (k3_xboole_0 @ X34 @ X36))
% 20.37/20.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34) @ 
% 20.37/20.60              (k2_zfmisc_1 @ X35 @ X36)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 20.37/20.60  thf('138', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.37/20.60         ((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X3 @ X0))
% 20.37/20.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X3) @ 
% 20.37/20.60              (k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['136', '137'])).
% 20.37/20.60  thf('139', plain,
% 20.37/20.60      (![X31 : $i, X32 : $i]:
% 20.37/20.60         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 20.37/20.60          | ((X31) != (k1_xboole_0)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 20.37/20.60  thf('140', plain,
% 20.37/20.60      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 20.37/20.60      inference('simplify', [status(thm)], ['139'])).
% 20.37/20.60  thf('141', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.37/20.60         ((k1_xboole_0)
% 20.37/20.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X3) @ 
% 20.37/20.60              (k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 20.37/20.60      inference('demod', [status(thm)], ['138', '140'])).
% 20.37/20.60  thf('142', plain,
% 20.37/20.60      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['126', '141'])).
% 20.37/20.60  thf('143', plain,
% 20.37/20.60      (((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 20.37/20.60         | ((k1_xboole_0) = (sk_B_1)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['115', '142'])).
% 20.37/20.60  thf('144', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.37/20.60  thf('145', plain,
% 20.37/20.60      ((((k1_xboole_0) = (sk_B_1))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 20.37/20.60      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 20.37/20.60  thf('146', plain,
% 20.37/20.60      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))
% 20.37/20.60        | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 20.37/20.60      inference('demod', [status(thm)], ['35', '36', '67'])).
% 20.37/20.60  thf('147', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k3_xboole_0 @ X1 @ X0)
% 20.37/20.60           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['84', '89'])).
% 20.37/20.60  thf('148', plain,
% 20.37/20.60      ((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 20.37/20.60        | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 20.37/20.60      inference('sup+', [status(thm)], ['146', '147'])).
% 20.37/20.60  thf('149', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.37/20.60  thf('150', plain,
% 20.37/20.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 20.37/20.60  thf('151', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('152', plain,
% 20.37/20.60      ((((k3_xboole_0 @ sk_D @ sk_B_1) = (sk_B_1))
% 20.37/20.60        | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 20.37/20.60      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 20.37/20.60  thf('153', plain,
% 20.37/20.60      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 20.37/20.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 20.37/20.60  thf('154', plain,
% 20.37/20.60      (((r1_tarski @ sk_B_1 @ sk_D) | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 20.37/20.60      inference('sup+', [status(thm)], ['152', '153'])).
% 20.37/20.60  thf('155', plain,
% 20.37/20.60      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 20.37/20.60      inference('split', [status(esa)], ['106'])).
% 20.37/20.60  thf('156', plain,
% 20.37/20.60      (((r1_xboole_0 @ sk_C_1 @ sk_A)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['154', '155'])).
% 20.37/20.60  thf('157', plain,
% 20.37/20.60      (![X4 : $i, X5 : $i]:
% 20.37/20.60         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 20.37/20.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 20.37/20.60  thf('158', plain,
% 20.37/20.60      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 20.37/20.60      inference('sup-', [status(thm)], ['156', '157'])).
% 20.37/20.60  thf('159', plain,
% 20.37/20.60      (![X0 : $i, X1 : $i]:
% 20.37/20.60         ((k4_xboole_0 @ X0 @ X1)
% 20.37/20.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['9', '10'])).
% 20.37/20.60  thf('160', plain,
% 20.37/20.60      ((((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0)))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['158', '159'])).
% 20.37/20.60  thf('161', plain,
% 20.37/20.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 20.37/20.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 20.37/20.60  thf('162', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.37/20.60      inference('sup+', [status(thm)], ['38', '39'])).
% 20.37/20.60  thf('163', plain,
% 20.37/20.60      ((((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A)))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 20.37/20.60      inference('demod', [status(thm)], ['160', '161', '162'])).
% 20.37/20.60  thf('164', plain,
% 20.37/20.60      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1))),
% 20.37/20.60      inference('sup+', [status(thm)], ['126', '141'])).
% 20.37/20.60  thf('165', plain,
% 20.37/20.60      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 20.37/20.60         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 20.37/20.60      inference('sup+', [status(thm)], ['163', '164'])).
% 20.37/20.60  thf('166', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 20.37/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.37/20.60  thf('167', plain, (((r1_tarski @ sk_B_1 @ sk_D))),
% 20.37/20.60      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 20.37/20.60  thf('168', plain,
% 20.37/20.60      (~ ((r1_tarski @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 20.37/20.60      inference('split', [status(esa)], ['106'])).
% 20.37/20.60  thf('169', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 20.37/20.60      inference('sat_resolution*', [status(thm)], ['167', '168'])).
% 20.37/20.60  thf('170', plain, (((k1_xboole_0) = (sk_B_1))),
% 20.37/20.60      inference('simpl_trail', [status(thm)], ['145', '169'])).
% 20.37/20.60  thf('171', plain,
% 20.37/20.60      (![X31 : $i, X32 : $i]:
% 20.37/20.60         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 20.37/20.60          | ((X32) != (k1_xboole_0)))),
% 20.37/20.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 20.37/20.60  thf('172', plain,
% 20.37/20.60      (![X31 : $i]: ((k2_zfmisc_1 @ X31 @ k1_xboole_0) = (k1_xboole_0))),
% 20.37/20.60      inference('simplify', [status(thm)], ['171'])).
% 20.37/20.60  thf('173', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 20.37/20.60      inference('demod', [status(thm)], ['0', '170', '172'])).
% 20.37/20.60  thf('174', plain, ($false), inference('simplify', [status(thm)], ['173'])).
% 20.37/20.60  
% 20.37/20.60  % SZS output end Refutation
% 20.37/20.60  
% 20.37/20.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
